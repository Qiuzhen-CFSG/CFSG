module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0ResidualSlices
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-2 residual group 2, transitions 174–179

Check each prescribed permutation identity on 29 slices of 140 points, then
assemble it with `Part0Residual.ofPointSlices`. Separate declarations bound
kernel reduction memory. Source: `OrderLevel0Data` and the transition enumeration
`Part2Residual.target` in `OrderLevel0Part2ResidualReduction`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part2Residual.Residual2Checks
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point174Slice0 : Part0Residual.pointSliceCheck 0 3267 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point174Slice1 : Part0Residual.pointSliceCheck 0 3267 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point174Slice2 : Part0Residual.pointSliceCheck 0 3267 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point174Slice3 : Part0Residual.pointSliceCheck 0 3267 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point174Slice4 : Part0Residual.pointSliceCheck 0 3267 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point174Slice5 : Part0Residual.pointSliceCheck 0 3267 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point174Slice6 : Part0Residual.pointSliceCheck 0 3267 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point174Slice7 : Part0Residual.pointSliceCheck 0 3267 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point174Slice8 : Part0Residual.pointSliceCheck 0 3267 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point174Slice9 : Part0Residual.pointSliceCheck 0 3267 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point174Slice10 : Part0Residual.pointSliceCheck 0 3267 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point174Slice11 : Part0Residual.pointSliceCheck 0 3267 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point174Slice12 : Part0Residual.pointSliceCheck 0 3267 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point174Slice13 : Part0Residual.pointSliceCheck 0 3267 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point174Slice14 : Part0Residual.pointSliceCheck 0 3267 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point174Slice15 : Part0Residual.pointSliceCheck 0 3267 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point174Slice16 : Part0Residual.pointSliceCheck 0 3267 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point174Slice17 : Part0Residual.pointSliceCheck 0 3267 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point174Slice18 : Part0Residual.pointSliceCheck 0 3267 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point174Slice19 : Part0Residual.pointSliceCheck 0 3267 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point174Slice20 : Part0Residual.pointSliceCheck 0 3267 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point174Slice21 : Part0Residual.pointSliceCheck 0 3267 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point174Slice22 : Part0Residual.pointSliceCheck 0 3267 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point174Slice23 : Part0Residual.pointSliceCheck 0 3267 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point174Slice24 : Part0Residual.pointSliceCheck 0 3267 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point174Slice25 : Part0Residual.pointSliceCheck 0 3267 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point174Slice26 : Part0Residual.pointSliceCheck 0 3267 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point174Slice27 : Part0Residual.pointSliceCheck 0 3267 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point174Slice28 : Part0Residual.pointSliceCheck 0 3267 28 := by
  decide +kernel

public theorem point174 : stepCheck 0 3267 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point174Slice0
  · exact point174Slice1
  · exact point174Slice2
  · exact point174Slice3
  · exact point174Slice4
  · exact point174Slice5
  · exact point174Slice6
  · exact point174Slice7
  · exact point174Slice8
  · exact point174Slice9
  · exact point174Slice10
  · exact point174Slice11
  · exact point174Slice12
  · exact point174Slice13
  · exact point174Slice14
  · exact point174Slice15
  · exact point174Slice16
  · exact point174Slice17
  · exact point174Slice18
  · exact point174Slice19
  · exact point174Slice20
  · exact point174Slice21
  · exact point174Slice22
  · exact point174Slice23
  · exact point174Slice24
  · exact point174Slice25
  · exact point174Slice26
  · exact point174Slice27
  · exact point174Slice28

set_option maxHeartbeats 1600000 in
private theorem point175Slice0 : Part0Residual.pointSliceCheck 0 3270 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point175Slice1 : Part0Residual.pointSliceCheck 0 3270 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point175Slice2 : Part0Residual.pointSliceCheck 0 3270 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point175Slice3 : Part0Residual.pointSliceCheck 0 3270 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point175Slice4 : Part0Residual.pointSliceCheck 0 3270 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point175Slice5 : Part0Residual.pointSliceCheck 0 3270 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point175Slice6 : Part0Residual.pointSliceCheck 0 3270 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point175Slice7 : Part0Residual.pointSliceCheck 0 3270 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point175Slice8 : Part0Residual.pointSliceCheck 0 3270 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point175Slice9 : Part0Residual.pointSliceCheck 0 3270 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point175Slice10 : Part0Residual.pointSliceCheck 0 3270 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point175Slice11 : Part0Residual.pointSliceCheck 0 3270 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point175Slice12 : Part0Residual.pointSliceCheck 0 3270 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point175Slice13 : Part0Residual.pointSliceCheck 0 3270 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point175Slice14 : Part0Residual.pointSliceCheck 0 3270 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point175Slice15 : Part0Residual.pointSliceCheck 0 3270 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point175Slice16 : Part0Residual.pointSliceCheck 0 3270 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point175Slice17 : Part0Residual.pointSliceCheck 0 3270 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point175Slice18 : Part0Residual.pointSliceCheck 0 3270 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point175Slice19 : Part0Residual.pointSliceCheck 0 3270 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point175Slice20 : Part0Residual.pointSliceCheck 0 3270 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point175Slice21 : Part0Residual.pointSliceCheck 0 3270 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point175Slice22 : Part0Residual.pointSliceCheck 0 3270 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point175Slice23 : Part0Residual.pointSliceCheck 0 3270 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point175Slice24 : Part0Residual.pointSliceCheck 0 3270 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point175Slice25 : Part0Residual.pointSliceCheck 0 3270 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point175Slice26 : Part0Residual.pointSliceCheck 0 3270 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point175Slice27 : Part0Residual.pointSliceCheck 0 3270 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point175Slice28 : Part0Residual.pointSliceCheck 0 3270 28 := by
  decide +kernel

public theorem point175 : stepCheck 0 3270 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point175Slice0
  · exact point175Slice1
  · exact point175Slice2
  · exact point175Slice3
  · exact point175Slice4
  · exact point175Slice5
  · exact point175Slice6
  · exact point175Slice7
  · exact point175Slice8
  · exact point175Slice9
  · exact point175Slice10
  · exact point175Slice11
  · exact point175Slice12
  · exact point175Slice13
  · exact point175Slice14
  · exact point175Slice15
  · exact point175Slice16
  · exact point175Slice17
  · exact point175Slice18
  · exact point175Slice19
  · exact point175Slice20
  · exact point175Slice21
  · exact point175Slice22
  · exact point175Slice23
  · exact point175Slice24
  · exact point175Slice25
  · exact point175Slice26
  · exact point175Slice27
  · exact point175Slice28

set_option maxHeartbeats 1600000 in
private theorem point176Slice0 : Part0Residual.pointSliceCheck 0 3271 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point176Slice1 : Part0Residual.pointSliceCheck 0 3271 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point176Slice2 : Part0Residual.pointSliceCheck 0 3271 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point176Slice3 : Part0Residual.pointSliceCheck 0 3271 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point176Slice4 : Part0Residual.pointSliceCheck 0 3271 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point176Slice5 : Part0Residual.pointSliceCheck 0 3271 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point176Slice6 : Part0Residual.pointSliceCheck 0 3271 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point176Slice7 : Part0Residual.pointSliceCheck 0 3271 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point176Slice8 : Part0Residual.pointSliceCheck 0 3271 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point176Slice9 : Part0Residual.pointSliceCheck 0 3271 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point176Slice10 : Part0Residual.pointSliceCheck 0 3271 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point176Slice11 : Part0Residual.pointSliceCheck 0 3271 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point176Slice12 : Part0Residual.pointSliceCheck 0 3271 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point176Slice13 : Part0Residual.pointSliceCheck 0 3271 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point176Slice14 : Part0Residual.pointSliceCheck 0 3271 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point176Slice15 : Part0Residual.pointSliceCheck 0 3271 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point176Slice16 : Part0Residual.pointSliceCheck 0 3271 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point176Slice17 : Part0Residual.pointSliceCheck 0 3271 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point176Slice18 : Part0Residual.pointSliceCheck 0 3271 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point176Slice19 : Part0Residual.pointSliceCheck 0 3271 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point176Slice20 : Part0Residual.pointSliceCheck 0 3271 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point176Slice21 : Part0Residual.pointSliceCheck 0 3271 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point176Slice22 : Part0Residual.pointSliceCheck 0 3271 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point176Slice23 : Part0Residual.pointSliceCheck 0 3271 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point176Slice24 : Part0Residual.pointSliceCheck 0 3271 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point176Slice25 : Part0Residual.pointSliceCheck 0 3271 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point176Slice26 : Part0Residual.pointSliceCheck 0 3271 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point176Slice27 : Part0Residual.pointSliceCheck 0 3271 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point176Slice28 : Part0Residual.pointSliceCheck 0 3271 28 := by
  decide +kernel

public theorem point176 : stepCheck 0 3271 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point176Slice0
  · exact point176Slice1
  · exact point176Slice2
  · exact point176Slice3
  · exact point176Slice4
  · exact point176Slice5
  · exact point176Slice6
  · exact point176Slice7
  · exact point176Slice8
  · exact point176Slice9
  · exact point176Slice10
  · exact point176Slice11
  · exact point176Slice12
  · exact point176Slice13
  · exact point176Slice14
  · exact point176Slice15
  · exact point176Slice16
  · exact point176Slice17
  · exact point176Slice18
  · exact point176Slice19
  · exact point176Slice20
  · exact point176Slice21
  · exact point176Slice22
  · exact point176Slice23
  · exact point176Slice24
  · exact point176Slice25
  · exact point176Slice26
  · exact point176Slice27
  · exact point176Slice28

set_option maxHeartbeats 1600000 in
private theorem point177Slice0 : Part0Residual.pointSliceCheck 0 3272 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point177Slice1 : Part0Residual.pointSliceCheck 0 3272 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point177Slice2 : Part0Residual.pointSliceCheck 0 3272 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point177Slice3 : Part0Residual.pointSliceCheck 0 3272 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point177Slice4 : Part0Residual.pointSliceCheck 0 3272 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point177Slice5 : Part0Residual.pointSliceCheck 0 3272 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point177Slice6 : Part0Residual.pointSliceCheck 0 3272 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point177Slice7 : Part0Residual.pointSliceCheck 0 3272 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point177Slice8 : Part0Residual.pointSliceCheck 0 3272 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point177Slice9 : Part0Residual.pointSliceCheck 0 3272 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point177Slice10 : Part0Residual.pointSliceCheck 0 3272 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point177Slice11 : Part0Residual.pointSliceCheck 0 3272 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point177Slice12 : Part0Residual.pointSliceCheck 0 3272 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point177Slice13 : Part0Residual.pointSliceCheck 0 3272 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point177Slice14 : Part0Residual.pointSliceCheck 0 3272 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point177Slice15 : Part0Residual.pointSliceCheck 0 3272 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point177Slice16 : Part0Residual.pointSliceCheck 0 3272 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point177Slice17 : Part0Residual.pointSliceCheck 0 3272 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point177Slice18 : Part0Residual.pointSliceCheck 0 3272 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point177Slice19 : Part0Residual.pointSliceCheck 0 3272 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point177Slice20 : Part0Residual.pointSliceCheck 0 3272 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point177Slice21 : Part0Residual.pointSliceCheck 0 3272 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point177Slice22 : Part0Residual.pointSliceCheck 0 3272 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point177Slice23 : Part0Residual.pointSliceCheck 0 3272 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point177Slice24 : Part0Residual.pointSliceCheck 0 3272 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point177Slice25 : Part0Residual.pointSliceCheck 0 3272 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point177Slice26 : Part0Residual.pointSliceCheck 0 3272 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point177Slice27 : Part0Residual.pointSliceCheck 0 3272 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point177Slice28 : Part0Residual.pointSliceCheck 0 3272 28 := by
  decide +kernel

public theorem point177 : stepCheck 0 3272 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point177Slice0
  · exact point177Slice1
  · exact point177Slice2
  · exact point177Slice3
  · exact point177Slice4
  · exact point177Slice5
  · exact point177Slice6
  · exact point177Slice7
  · exact point177Slice8
  · exact point177Slice9
  · exact point177Slice10
  · exact point177Slice11
  · exact point177Slice12
  · exact point177Slice13
  · exact point177Slice14
  · exact point177Slice15
  · exact point177Slice16
  · exact point177Slice17
  · exact point177Slice18
  · exact point177Slice19
  · exact point177Slice20
  · exact point177Slice21
  · exact point177Slice22
  · exact point177Slice23
  · exact point177Slice24
  · exact point177Slice25
  · exact point177Slice26
  · exact point177Slice27
  · exact point177Slice28

set_option maxHeartbeats 1600000 in
private theorem point178Slice0 : Part0Residual.pointSliceCheck 0 3273 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point178Slice1 : Part0Residual.pointSliceCheck 0 3273 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point178Slice2 : Part0Residual.pointSliceCheck 0 3273 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point178Slice3 : Part0Residual.pointSliceCheck 0 3273 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point178Slice4 : Part0Residual.pointSliceCheck 0 3273 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point178Slice5 : Part0Residual.pointSliceCheck 0 3273 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point178Slice6 : Part0Residual.pointSliceCheck 0 3273 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point178Slice7 : Part0Residual.pointSliceCheck 0 3273 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point178Slice8 : Part0Residual.pointSliceCheck 0 3273 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point178Slice9 : Part0Residual.pointSliceCheck 0 3273 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point178Slice10 : Part0Residual.pointSliceCheck 0 3273 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point178Slice11 : Part0Residual.pointSliceCheck 0 3273 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point178Slice12 : Part0Residual.pointSliceCheck 0 3273 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point178Slice13 : Part0Residual.pointSliceCheck 0 3273 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point178Slice14 : Part0Residual.pointSliceCheck 0 3273 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point178Slice15 : Part0Residual.pointSliceCheck 0 3273 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point178Slice16 : Part0Residual.pointSliceCheck 0 3273 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point178Slice17 : Part0Residual.pointSliceCheck 0 3273 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point178Slice18 : Part0Residual.pointSliceCheck 0 3273 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point178Slice19 : Part0Residual.pointSliceCheck 0 3273 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point178Slice20 : Part0Residual.pointSliceCheck 0 3273 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point178Slice21 : Part0Residual.pointSliceCheck 0 3273 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point178Slice22 : Part0Residual.pointSliceCheck 0 3273 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point178Slice23 : Part0Residual.pointSliceCheck 0 3273 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point178Slice24 : Part0Residual.pointSliceCheck 0 3273 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point178Slice25 : Part0Residual.pointSliceCheck 0 3273 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point178Slice26 : Part0Residual.pointSliceCheck 0 3273 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point178Slice27 : Part0Residual.pointSliceCheck 0 3273 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point178Slice28 : Part0Residual.pointSliceCheck 0 3273 28 := by
  decide +kernel

public theorem point178 : stepCheck 0 3273 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point178Slice0
  · exact point178Slice1
  · exact point178Slice2
  · exact point178Slice3
  · exact point178Slice4
  · exact point178Slice5
  · exact point178Slice6
  · exact point178Slice7
  · exact point178Slice8
  · exact point178Slice9
  · exact point178Slice10
  · exact point178Slice11
  · exact point178Slice12
  · exact point178Slice13
  · exact point178Slice14
  · exact point178Slice15
  · exact point178Slice16
  · exact point178Slice17
  · exact point178Slice18
  · exact point178Slice19
  · exact point178Slice20
  · exact point178Slice21
  · exact point178Slice22
  · exact point178Slice23
  · exact point178Slice24
  · exact point178Slice25
  · exact point178Slice26
  · exact point178Slice27
  · exact point178Slice28

set_option maxHeartbeats 1600000 in
private theorem point179Slice0 : Part0Residual.pointSliceCheck 0 3274 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point179Slice1 : Part0Residual.pointSliceCheck 0 3274 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point179Slice2 : Part0Residual.pointSliceCheck 0 3274 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point179Slice3 : Part0Residual.pointSliceCheck 0 3274 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point179Slice4 : Part0Residual.pointSliceCheck 0 3274 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point179Slice5 : Part0Residual.pointSliceCheck 0 3274 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point179Slice6 : Part0Residual.pointSliceCheck 0 3274 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point179Slice7 : Part0Residual.pointSliceCheck 0 3274 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point179Slice8 : Part0Residual.pointSliceCheck 0 3274 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point179Slice9 : Part0Residual.pointSliceCheck 0 3274 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point179Slice10 : Part0Residual.pointSliceCheck 0 3274 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point179Slice11 : Part0Residual.pointSliceCheck 0 3274 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point179Slice12 : Part0Residual.pointSliceCheck 0 3274 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point179Slice13 : Part0Residual.pointSliceCheck 0 3274 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point179Slice14 : Part0Residual.pointSliceCheck 0 3274 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point179Slice15 : Part0Residual.pointSliceCheck 0 3274 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point179Slice16 : Part0Residual.pointSliceCheck 0 3274 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point179Slice17 : Part0Residual.pointSliceCheck 0 3274 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point179Slice18 : Part0Residual.pointSliceCheck 0 3274 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point179Slice19 : Part0Residual.pointSliceCheck 0 3274 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point179Slice20 : Part0Residual.pointSliceCheck 0 3274 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point179Slice21 : Part0Residual.pointSliceCheck 0 3274 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point179Slice22 : Part0Residual.pointSliceCheck 0 3274 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point179Slice23 : Part0Residual.pointSliceCheck 0 3274 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point179Slice24 : Part0Residual.pointSliceCheck 0 3274 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point179Slice25 : Part0Residual.pointSliceCheck 0 3274 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point179Slice26 : Part0Residual.pointSliceCheck 0 3274 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point179Slice27 : Part0Residual.pointSliceCheck 0 3274 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point179Slice28 : Part0Residual.pointSliceCheck 0 3274 28 := by
  decide +kernel

public theorem point179 : stepCheck 0 3274 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point179Slice0
  · exact point179Slice1
  · exact point179Slice2
  · exact point179Slice3
  · exact point179Slice4
  · exact point179Slice5
  · exact point179Slice6
  · exact point179Slice7
  · exact point179Slice8
  · exact point179Slice9
  · exact point179Slice10
  · exact point179Slice11
  · exact point179Slice12
  · exact point179Slice13
  · exact point179Slice14
  · exact point179Slice15
  · exact point179Slice16
  · exact point179Slice17
  · exact point179Slice18
  · exact point179Slice19
  · exact point179Slice20
  · exact point179Slice21
  · exact point179Slice22
  · exact point179Slice23
  · exact point179Slice24
  · exact point179Slice25
  · exact point179Slice26
  · exact point179Slice27
  · exact point179Slice28

end Rudvalis.OrderCertificate.ForwardReduction.Part2Residual.Residual2Checks
