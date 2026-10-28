module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0ResidualSlices
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-2 residual group 2, transitions 150–155

Check each prescribed permutation identity on 29 slices of 140 points, then
assemble it with `Part0Residual.ofPointSlices`. Separate declarations bound
kernel reduction memory. Source: `OrderLevel0Data` and the transition enumeration
`Part2Residual.target` in `OrderLevel0Part2ResidualReduction`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part2Residual.Residual2Checks
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point150Slice0 : Part0Residual.pointSliceCheck 0 2989 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point150Slice1 : Part0Residual.pointSliceCheck 0 2989 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point150Slice2 : Part0Residual.pointSliceCheck 0 2989 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point150Slice3 : Part0Residual.pointSliceCheck 0 2989 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point150Slice4 : Part0Residual.pointSliceCheck 0 2989 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point150Slice5 : Part0Residual.pointSliceCheck 0 2989 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point150Slice6 : Part0Residual.pointSliceCheck 0 2989 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point150Slice7 : Part0Residual.pointSliceCheck 0 2989 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point150Slice8 : Part0Residual.pointSliceCheck 0 2989 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point150Slice9 : Part0Residual.pointSliceCheck 0 2989 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point150Slice10 : Part0Residual.pointSliceCheck 0 2989 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point150Slice11 : Part0Residual.pointSliceCheck 0 2989 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point150Slice12 : Part0Residual.pointSliceCheck 0 2989 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point150Slice13 : Part0Residual.pointSliceCheck 0 2989 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point150Slice14 : Part0Residual.pointSliceCheck 0 2989 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point150Slice15 : Part0Residual.pointSliceCheck 0 2989 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point150Slice16 : Part0Residual.pointSliceCheck 0 2989 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point150Slice17 : Part0Residual.pointSliceCheck 0 2989 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point150Slice18 : Part0Residual.pointSliceCheck 0 2989 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point150Slice19 : Part0Residual.pointSliceCheck 0 2989 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point150Slice20 : Part0Residual.pointSliceCheck 0 2989 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point150Slice21 : Part0Residual.pointSliceCheck 0 2989 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point150Slice22 : Part0Residual.pointSliceCheck 0 2989 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point150Slice23 : Part0Residual.pointSliceCheck 0 2989 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point150Slice24 : Part0Residual.pointSliceCheck 0 2989 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point150Slice25 : Part0Residual.pointSliceCheck 0 2989 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point150Slice26 : Part0Residual.pointSliceCheck 0 2989 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point150Slice27 : Part0Residual.pointSliceCheck 0 2989 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point150Slice28 : Part0Residual.pointSliceCheck 0 2989 28 := by
  decide +kernel

public theorem point150 : stepCheck 0 2989 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point150Slice0
  · exact point150Slice1
  · exact point150Slice2
  · exact point150Slice3
  · exact point150Slice4
  · exact point150Slice5
  · exact point150Slice6
  · exact point150Slice7
  · exact point150Slice8
  · exact point150Slice9
  · exact point150Slice10
  · exact point150Slice11
  · exact point150Slice12
  · exact point150Slice13
  · exact point150Slice14
  · exact point150Slice15
  · exact point150Slice16
  · exact point150Slice17
  · exact point150Slice18
  · exact point150Slice19
  · exact point150Slice20
  · exact point150Slice21
  · exact point150Slice22
  · exact point150Slice23
  · exact point150Slice24
  · exact point150Slice25
  · exact point150Slice26
  · exact point150Slice27
  · exact point150Slice28

set_option maxHeartbeats 1600000 in
private theorem point151Slice0 : Part0Residual.pointSliceCheck 0 2992 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point151Slice1 : Part0Residual.pointSliceCheck 0 2992 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point151Slice2 : Part0Residual.pointSliceCheck 0 2992 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point151Slice3 : Part0Residual.pointSliceCheck 0 2992 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point151Slice4 : Part0Residual.pointSliceCheck 0 2992 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point151Slice5 : Part0Residual.pointSliceCheck 0 2992 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point151Slice6 : Part0Residual.pointSliceCheck 0 2992 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point151Slice7 : Part0Residual.pointSliceCheck 0 2992 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point151Slice8 : Part0Residual.pointSliceCheck 0 2992 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point151Slice9 : Part0Residual.pointSliceCheck 0 2992 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point151Slice10 : Part0Residual.pointSliceCheck 0 2992 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point151Slice11 : Part0Residual.pointSliceCheck 0 2992 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point151Slice12 : Part0Residual.pointSliceCheck 0 2992 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point151Slice13 : Part0Residual.pointSliceCheck 0 2992 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point151Slice14 : Part0Residual.pointSliceCheck 0 2992 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point151Slice15 : Part0Residual.pointSliceCheck 0 2992 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point151Slice16 : Part0Residual.pointSliceCheck 0 2992 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point151Slice17 : Part0Residual.pointSliceCheck 0 2992 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point151Slice18 : Part0Residual.pointSliceCheck 0 2992 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point151Slice19 : Part0Residual.pointSliceCheck 0 2992 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point151Slice20 : Part0Residual.pointSliceCheck 0 2992 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point151Slice21 : Part0Residual.pointSliceCheck 0 2992 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point151Slice22 : Part0Residual.pointSliceCheck 0 2992 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point151Slice23 : Part0Residual.pointSliceCheck 0 2992 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point151Slice24 : Part0Residual.pointSliceCheck 0 2992 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point151Slice25 : Part0Residual.pointSliceCheck 0 2992 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point151Slice26 : Part0Residual.pointSliceCheck 0 2992 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point151Slice27 : Part0Residual.pointSliceCheck 0 2992 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point151Slice28 : Part0Residual.pointSliceCheck 0 2992 28 := by
  decide +kernel

public theorem point151 : stepCheck 0 2992 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point151Slice0
  · exact point151Slice1
  · exact point151Slice2
  · exact point151Slice3
  · exact point151Slice4
  · exact point151Slice5
  · exact point151Slice6
  · exact point151Slice7
  · exact point151Slice8
  · exact point151Slice9
  · exact point151Slice10
  · exact point151Slice11
  · exact point151Slice12
  · exact point151Slice13
  · exact point151Slice14
  · exact point151Slice15
  · exact point151Slice16
  · exact point151Slice17
  · exact point151Slice18
  · exact point151Slice19
  · exact point151Slice20
  · exact point151Slice21
  · exact point151Slice22
  · exact point151Slice23
  · exact point151Slice24
  · exact point151Slice25
  · exact point151Slice26
  · exact point151Slice27
  · exact point151Slice28

set_option maxHeartbeats 1600000 in
private theorem point152Slice0 : Part0Residual.pointSliceCheck 0 2993 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point152Slice1 : Part0Residual.pointSliceCheck 0 2993 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point152Slice2 : Part0Residual.pointSliceCheck 0 2993 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point152Slice3 : Part0Residual.pointSliceCheck 0 2993 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point152Slice4 : Part0Residual.pointSliceCheck 0 2993 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point152Slice5 : Part0Residual.pointSliceCheck 0 2993 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point152Slice6 : Part0Residual.pointSliceCheck 0 2993 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point152Slice7 : Part0Residual.pointSliceCheck 0 2993 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point152Slice8 : Part0Residual.pointSliceCheck 0 2993 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point152Slice9 : Part0Residual.pointSliceCheck 0 2993 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point152Slice10 : Part0Residual.pointSliceCheck 0 2993 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point152Slice11 : Part0Residual.pointSliceCheck 0 2993 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point152Slice12 : Part0Residual.pointSliceCheck 0 2993 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point152Slice13 : Part0Residual.pointSliceCheck 0 2993 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point152Slice14 : Part0Residual.pointSliceCheck 0 2993 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point152Slice15 : Part0Residual.pointSliceCheck 0 2993 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point152Slice16 : Part0Residual.pointSliceCheck 0 2993 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point152Slice17 : Part0Residual.pointSliceCheck 0 2993 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point152Slice18 : Part0Residual.pointSliceCheck 0 2993 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point152Slice19 : Part0Residual.pointSliceCheck 0 2993 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point152Slice20 : Part0Residual.pointSliceCheck 0 2993 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point152Slice21 : Part0Residual.pointSliceCheck 0 2993 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point152Slice22 : Part0Residual.pointSliceCheck 0 2993 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point152Slice23 : Part0Residual.pointSliceCheck 0 2993 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point152Slice24 : Part0Residual.pointSliceCheck 0 2993 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point152Slice25 : Part0Residual.pointSliceCheck 0 2993 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point152Slice26 : Part0Residual.pointSliceCheck 0 2993 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point152Slice27 : Part0Residual.pointSliceCheck 0 2993 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point152Slice28 : Part0Residual.pointSliceCheck 0 2993 28 := by
  decide +kernel

public theorem point152 : stepCheck 0 2993 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point152Slice0
  · exact point152Slice1
  · exact point152Slice2
  · exact point152Slice3
  · exact point152Slice4
  · exact point152Slice5
  · exact point152Slice6
  · exact point152Slice7
  · exact point152Slice8
  · exact point152Slice9
  · exact point152Slice10
  · exact point152Slice11
  · exact point152Slice12
  · exact point152Slice13
  · exact point152Slice14
  · exact point152Slice15
  · exact point152Slice16
  · exact point152Slice17
  · exact point152Slice18
  · exact point152Slice19
  · exact point152Slice20
  · exact point152Slice21
  · exact point152Slice22
  · exact point152Slice23
  · exact point152Slice24
  · exact point152Slice25
  · exact point152Slice26
  · exact point152Slice27
  · exact point152Slice28

set_option maxHeartbeats 1600000 in
private theorem point153Slice0 : Part0Residual.pointSliceCheck 0 2995 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point153Slice1 : Part0Residual.pointSliceCheck 0 2995 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point153Slice2 : Part0Residual.pointSliceCheck 0 2995 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point153Slice3 : Part0Residual.pointSliceCheck 0 2995 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point153Slice4 : Part0Residual.pointSliceCheck 0 2995 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point153Slice5 : Part0Residual.pointSliceCheck 0 2995 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point153Slice6 : Part0Residual.pointSliceCheck 0 2995 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point153Slice7 : Part0Residual.pointSliceCheck 0 2995 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point153Slice8 : Part0Residual.pointSliceCheck 0 2995 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point153Slice9 : Part0Residual.pointSliceCheck 0 2995 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point153Slice10 : Part0Residual.pointSliceCheck 0 2995 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point153Slice11 : Part0Residual.pointSliceCheck 0 2995 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point153Slice12 : Part0Residual.pointSliceCheck 0 2995 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point153Slice13 : Part0Residual.pointSliceCheck 0 2995 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point153Slice14 : Part0Residual.pointSliceCheck 0 2995 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point153Slice15 : Part0Residual.pointSliceCheck 0 2995 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point153Slice16 : Part0Residual.pointSliceCheck 0 2995 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point153Slice17 : Part0Residual.pointSliceCheck 0 2995 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point153Slice18 : Part0Residual.pointSliceCheck 0 2995 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point153Slice19 : Part0Residual.pointSliceCheck 0 2995 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point153Slice20 : Part0Residual.pointSliceCheck 0 2995 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point153Slice21 : Part0Residual.pointSliceCheck 0 2995 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point153Slice22 : Part0Residual.pointSliceCheck 0 2995 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point153Slice23 : Part0Residual.pointSliceCheck 0 2995 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point153Slice24 : Part0Residual.pointSliceCheck 0 2995 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point153Slice25 : Part0Residual.pointSliceCheck 0 2995 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point153Slice26 : Part0Residual.pointSliceCheck 0 2995 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point153Slice27 : Part0Residual.pointSliceCheck 0 2995 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point153Slice28 : Part0Residual.pointSliceCheck 0 2995 28 := by
  decide +kernel

public theorem point153 : stepCheck 0 2995 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point153Slice0
  · exact point153Slice1
  · exact point153Slice2
  · exact point153Slice3
  · exact point153Slice4
  · exact point153Slice5
  · exact point153Slice6
  · exact point153Slice7
  · exact point153Slice8
  · exact point153Slice9
  · exact point153Slice10
  · exact point153Slice11
  · exact point153Slice12
  · exact point153Slice13
  · exact point153Slice14
  · exact point153Slice15
  · exact point153Slice16
  · exact point153Slice17
  · exact point153Slice18
  · exact point153Slice19
  · exact point153Slice20
  · exact point153Slice21
  · exact point153Slice22
  · exact point153Slice23
  · exact point153Slice24
  · exact point153Slice25
  · exact point153Slice26
  · exact point153Slice27
  · exact point153Slice28

set_option maxHeartbeats 1600000 in
private theorem point154Slice0 : Part0Residual.pointSliceCheck 1 2984 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point154Slice1 : Part0Residual.pointSliceCheck 1 2984 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point154Slice2 : Part0Residual.pointSliceCheck 1 2984 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point154Slice3 : Part0Residual.pointSliceCheck 1 2984 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point154Slice4 : Part0Residual.pointSliceCheck 1 2984 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point154Slice5 : Part0Residual.pointSliceCheck 1 2984 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point154Slice6 : Part0Residual.pointSliceCheck 1 2984 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point154Slice7 : Part0Residual.pointSliceCheck 1 2984 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point154Slice8 : Part0Residual.pointSliceCheck 1 2984 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point154Slice9 : Part0Residual.pointSliceCheck 1 2984 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point154Slice10 : Part0Residual.pointSliceCheck 1 2984 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point154Slice11 : Part0Residual.pointSliceCheck 1 2984 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point154Slice12 : Part0Residual.pointSliceCheck 1 2984 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point154Slice13 : Part0Residual.pointSliceCheck 1 2984 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point154Slice14 : Part0Residual.pointSliceCheck 1 2984 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point154Slice15 : Part0Residual.pointSliceCheck 1 2984 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point154Slice16 : Part0Residual.pointSliceCheck 1 2984 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point154Slice17 : Part0Residual.pointSliceCheck 1 2984 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point154Slice18 : Part0Residual.pointSliceCheck 1 2984 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point154Slice19 : Part0Residual.pointSliceCheck 1 2984 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point154Slice20 : Part0Residual.pointSliceCheck 1 2984 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point154Slice21 : Part0Residual.pointSliceCheck 1 2984 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point154Slice22 : Part0Residual.pointSliceCheck 1 2984 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point154Slice23 : Part0Residual.pointSliceCheck 1 2984 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point154Slice24 : Part0Residual.pointSliceCheck 1 2984 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point154Slice25 : Part0Residual.pointSliceCheck 1 2984 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point154Slice26 : Part0Residual.pointSliceCheck 1 2984 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point154Slice27 : Part0Residual.pointSliceCheck 1 2984 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point154Slice28 : Part0Residual.pointSliceCheck 1 2984 28 := by
  decide +kernel

public theorem point154 : stepCheck 1 2984 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point154Slice0
  · exact point154Slice1
  · exact point154Slice2
  · exact point154Slice3
  · exact point154Slice4
  · exact point154Slice5
  · exact point154Slice6
  · exact point154Slice7
  · exact point154Slice8
  · exact point154Slice9
  · exact point154Slice10
  · exact point154Slice11
  · exact point154Slice12
  · exact point154Slice13
  · exact point154Slice14
  · exact point154Slice15
  · exact point154Slice16
  · exact point154Slice17
  · exact point154Slice18
  · exact point154Slice19
  · exact point154Slice20
  · exact point154Slice21
  · exact point154Slice22
  · exact point154Slice23
  · exact point154Slice24
  · exact point154Slice25
  · exact point154Slice26
  · exact point154Slice27
  · exact point154Slice28

set_option maxHeartbeats 1600000 in
private theorem point155Slice0 : Part0Residual.pointSliceCheck 1 2986 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point155Slice1 : Part0Residual.pointSliceCheck 1 2986 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point155Slice2 : Part0Residual.pointSliceCheck 1 2986 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point155Slice3 : Part0Residual.pointSliceCheck 1 2986 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point155Slice4 : Part0Residual.pointSliceCheck 1 2986 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point155Slice5 : Part0Residual.pointSliceCheck 1 2986 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point155Slice6 : Part0Residual.pointSliceCheck 1 2986 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point155Slice7 : Part0Residual.pointSliceCheck 1 2986 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point155Slice8 : Part0Residual.pointSliceCheck 1 2986 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point155Slice9 : Part0Residual.pointSliceCheck 1 2986 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point155Slice10 : Part0Residual.pointSliceCheck 1 2986 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point155Slice11 : Part0Residual.pointSliceCheck 1 2986 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point155Slice12 : Part0Residual.pointSliceCheck 1 2986 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point155Slice13 : Part0Residual.pointSliceCheck 1 2986 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point155Slice14 : Part0Residual.pointSliceCheck 1 2986 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point155Slice15 : Part0Residual.pointSliceCheck 1 2986 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point155Slice16 : Part0Residual.pointSliceCheck 1 2986 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point155Slice17 : Part0Residual.pointSliceCheck 1 2986 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point155Slice18 : Part0Residual.pointSliceCheck 1 2986 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point155Slice19 : Part0Residual.pointSliceCheck 1 2986 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point155Slice20 : Part0Residual.pointSliceCheck 1 2986 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point155Slice21 : Part0Residual.pointSliceCheck 1 2986 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point155Slice22 : Part0Residual.pointSliceCheck 1 2986 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point155Slice23 : Part0Residual.pointSliceCheck 1 2986 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point155Slice24 : Part0Residual.pointSliceCheck 1 2986 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point155Slice25 : Part0Residual.pointSliceCheck 1 2986 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point155Slice26 : Part0Residual.pointSliceCheck 1 2986 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point155Slice27 : Part0Residual.pointSliceCheck 1 2986 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point155Slice28 : Part0Residual.pointSliceCheck 1 2986 28 := by
  decide +kernel

public theorem point155 : stepCheck 1 2986 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point155Slice0
  · exact point155Slice1
  · exact point155Slice2
  · exact point155Slice3
  · exact point155Slice4
  · exact point155Slice5
  · exact point155Slice6
  · exact point155Slice7
  · exact point155Slice8
  · exact point155Slice9
  · exact point155Slice10
  · exact point155Slice11
  · exact point155Slice12
  · exact point155Slice13
  · exact point155Slice14
  · exact point155Slice15
  · exact point155Slice16
  · exact point155Slice17
  · exact point155Slice18
  · exact point155Slice19
  · exact point155Slice20
  · exact point155Slice21
  · exact point155Slice22
  · exact point155Slice23
  · exact point155Slice24
  · exact point155Slice25
  · exact point155Slice26
  · exact point155Slice27
  · exact point155Slice28

end Rudvalis.OrderCertificate.ForwardReduction.Part2Residual.Residual2Checks
