module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part1Residual0.Slices
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-1 residual group 0: independently checked transitions

Check the original permutation identities on 29 slices of 140 points and
assemble them with `ofPointSlices`. Separate declarations bound kernel memory.
Source: `OrderLevel0Data` and `OrderLevel0Part1ResidualReduction.target`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part1Residual.Residual0Checks
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point0Slice0 : pointSliceCheck 1 303 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0Slice1 : pointSliceCheck 1 303 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0Slice2 : pointSliceCheck 1 303 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0Slice3 : pointSliceCheck 1 303 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0Slice4 : pointSliceCheck 1 303 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0Slice5 : pointSliceCheck 1 303 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0Slice6 : pointSliceCheck 1 303 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0Slice7 : pointSliceCheck 1 303 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0Slice8 : pointSliceCheck 1 303 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0Slice9 : pointSliceCheck 1 303 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0Slice10 : pointSliceCheck 1 303 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0Slice11 : pointSliceCheck 1 303 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0Slice12 : pointSliceCheck 1 303 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0Slice13 : pointSliceCheck 1 303 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0Slice14 : pointSliceCheck 1 303 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0Slice15 : pointSliceCheck 1 303 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0Slice16 : pointSliceCheck 1 303 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0Slice17 : pointSliceCheck 1 303 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0Slice18 : pointSliceCheck 1 303 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0Slice19 : pointSliceCheck 1 303 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0Slice20 : pointSliceCheck 1 303 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0Slice21 : pointSliceCheck 1 303 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0Slice22 : pointSliceCheck 1 303 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0Slice23 : pointSliceCheck 1 303 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0Slice24 : pointSliceCheck 1 303 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0Slice25 : pointSliceCheck 1 303 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0Slice26 : pointSliceCheck 1 303 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0Slice27 : pointSliceCheck 1 303 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0Slice28 : pointSliceCheck 1 303 28 := by
  decide +kernel

public theorem point0 : residualCheck 0 := by
  apply ofPointSlices 1 303
  intro c
  fin_cases c
  · exact point0Slice0
  · exact point0Slice1
  · exact point0Slice2
  · exact point0Slice3
  · exact point0Slice4
  · exact point0Slice5
  · exact point0Slice6
  · exact point0Slice7
  · exact point0Slice8
  · exact point0Slice9
  · exact point0Slice10
  · exact point0Slice11
  · exact point0Slice12
  · exact point0Slice13
  · exact point0Slice14
  · exact point0Slice15
  · exact point0Slice16
  · exact point0Slice17
  · exact point0Slice18
  · exact point0Slice19
  · exact point0Slice20
  · exact point0Slice21
  · exact point0Slice22
  · exact point0Slice23
  · exact point0Slice24
  · exact point0Slice25
  · exact point0Slice26
  · exact point0Slice27
  · exact point0Slice28

set_option maxHeartbeats 1600000 in
private theorem point1Slice0 : pointSliceCheck 1 317 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1Slice1 : pointSliceCheck 1 317 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1Slice2 : pointSliceCheck 1 317 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1Slice3 : pointSliceCheck 1 317 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1Slice4 : pointSliceCheck 1 317 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1Slice5 : pointSliceCheck 1 317 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1Slice6 : pointSliceCheck 1 317 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1Slice7 : pointSliceCheck 1 317 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1Slice8 : pointSliceCheck 1 317 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1Slice9 : pointSliceCheck 1 317 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1Slice10 : pointSliceCheck 1 317 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1Slice11 : pointSliceCheck 1 317 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1Slice12 : pointSliceCheck 1 317 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1Slice13 : pointSliceCheck 1 317 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1Slice14 : pointSliceCheck 1 317 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1Slice15 : pointSliceCheck 1 317 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1Slice16 : pointSliceCheck 1 317 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1Slice17 : pointSliceCheck 1 317 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1Slice18 : pointSliceCheck 1 317 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1Slice19 : pointSliceCheck 1 317 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1Slice20 : pointSliceCheck 1 317 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1Slice21 : pointSliceCheck 1 317 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1Slice22 : pointSliceCheck 1 317 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1Slice23 : pointSliceCheck 1 317 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1Slice24 : pointSliceCheck 1 317 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1Slice25 : pointSliceCheck 1 317 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1Slice26 : pointSliceCheck 1 317 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1Slice27 : pointSliceCheck 1 317 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1Slice28 : pointSliceCheck 1 317 28 := by
  decide +kernel

public theorem point1 : residualCheck 1 := by
  apply ofPointSlices 1 317
  intro c
  fin_cases c
  · exact point1Slice0
  · exact point1Slice1
  · exact point1Slice2
  · exact point1Slice3
  · exact point1Slice4
  · exact point1Slice5
  · exact point1Slice6
  · exact point1Slice7
  · exact point1Slice8
  · exact point1Slice9
  · exact point1Slice10
  · exact point1Slice11
  · exact point1Slice12
  · exact point1Slice13
  · exact point1Slice14
  · exact point1Slice15
  · exact point1Slice16
  · exact point1Slice17
  · exact point1Slice18
  · exact point1Slice19
  · exact point1Slice20
  · exact point1Slice21
  · exact point1Slice22
  · exact point1Slice23
  · exact point1Slice24
  · exact point1Slice25
  · exact point1Slice26
  · exact point1Slice27
  · exact point1Slice28

set_option maxHeartbeats 1600000 in
private theorem point2Slice0 : pointSliceCheck 1 440 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2Slice1 : pointSliceCheck 1 440 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2Slice2 : pointSliceCheck 1 440 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2Slice3 : pointSliceCheck 1 440 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2Slice4 : pointSliceCheck 1 440 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2Slice5 : pointSliceCheck 1 440 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2Slice6 : pointSliceCheck 1 440 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2Slice7 : pointSliceCheck 1 440 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2Slice8 : pointSliceCheck 1 440 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2Slice9 : pointSliceCheck 1 440 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2Slice10 : pointSliceCheck 1 440 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2Slice11 : pointSliceCheck 1 440 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2Slice12 : pointSliceCheck 1 440 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2Slice13 : pointSliceCheck 1 440 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2Slice14 : pointSliceCheck 1 440 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2Slice15 : pointSliceCheck 1 440 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2Slice16 : pointSliceCheck 1 440 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2Slice17 : pointSliceCheck 1 440 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2Slice18 : pointSliceCheck 1 440 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2Slice19 : pointSliceCheck 1 440 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2Slice20 : pointSliceCheck 1 440 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2Slice21 : pointSliceCheck 1 440 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2Slice22 : pointSliceCheck 1 440 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2Slice23 : pointSliceCheck 1 440 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2Slice24 : pointSliceCheck 1 440 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2Slice25 : pointSliceCheck 1 440 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2Slice26 : pointSliceCheck 1 440 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2Slice27 : pointSliceCheck 1 440 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2Slice28 : pointSliceCheck 1 440 28 := by
  decide +kernel

public theorem point2 : residualCheck 2 := by
  apply ofPointSlices 1 440
  intro c
  fin_cases c
  · exact point2Slice0
  · exact point2Slice1
  · exact point2Slice2
  · exact point2Slice3
  · exact point2Slice4
  · exact point2Slice5
  · exact point2Slice6
  · exact point2Slice7
  · exact point2Slice8
  · exact point2Slice9
  · exact point2Slice10
  · exact point2Slice11
  · exact point2Slice12
  · exact point2Slice13
  · exact point2Slice14
  · exact point2Slice15
  · exact point2Slice16
  · exact point2Slice17
  · exact point2Slice18
  · exact point2Slice19
  · exact point2Slice20
  · exact point2Slice21
  · exact point2Slice22
  · exact point2Slice23
  · exact point2Slice24
  · exact point2Slice25
  · exact point2Slice26
  · exact point2Slice27
  · exact point2Slice28

set_option maxHeartbeats 1600000 in
private theorem point3Slice0 : pointSliceCheck 0 584 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3Slice1 : pointSliceCheck 0 584 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3Slice2 : pointSliceCheck 0 584 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3Slice3 : pointSliceCheck 0 584 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3Slice4 : pointSliceCheck 0 584 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3Slice5 : pointSliceCheck 0 584 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3Slice6 : pointSliceCheck 0 584 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3Slice7 : pointSliceCheck 0 584 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3Slice8 : pointSliceCheck 0 584 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3Slice9 : pointSliceCheck 0 584 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3Slice10 : pointSliceCheck 0 584 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3Slice11 : pointSliceCheck 0 584 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3Slice12 : pointSliceCheck 0 584 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3Slice13 : pointSliceCheck 0 584 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3Slice14 : pointSliceCheck 0 584 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3Slice15 : pointSliceCheck 0 584 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3Slice16 : pointSliceCheck 0 584 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3Slice17 : pointSliceCheck 0 584 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3Slice18 : pointSliceCheck 0 584 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3Slice19 : pointSliceCheck 0 584 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3Slice20 : pointSliceCheck 0 584 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3Slice21 : pointSliceCheck 0 584 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3Slice22 : pointSliceCheck 0 584 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3Slice23 : pointSliceCheck 0 584 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3Slice24 : pointSliceCheck 0 584 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3Slice25 : pointSliceCheck 0 584 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3Slice26 : pointSliceCheck 0 584 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3Slice27 : pointSliceCheck 0 584 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3Slice28 : pointSliceCheck 0 584 28 := by
  decide +kernel

public theorem point3 : residualCheck 3 := by
  apply ofPointSlices 0 584
  intro c
  fin_cases c
  · exact point3Slice0
  · exact point3Slice1
  · exact point3Slice2
  · exact point3Slice3
  · exact point3Slice4
  · exact point3Slice5
  · exact point3Slice6
  · exact point3Slice7
  · exact point3Slice8
  · exact point3Slice9
  · exact point3Slice10
  · exact point3Slice11
  · exact point3Slice12
  · exact point3Slice13
  · exact point3Slice14
  · exact point3Slice15
  · exact point3Slice16
  · exact point3Slice17
  · exact point3Slice18
  · exact point3Slice19
  · exact point3Slice20
  · exact point3Slice21
  · exact point3Slice22
  · exact point3Slice23
  · exact point3Slice24
  · exact point3Slice25
  · exact point3Slice26
  · exact point3Slice27
  · exact point3Slice28

set_option maxHeartbeats 1600000 in
private theorem point4Slice0 : pointSliceCheck 0 595 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4Slice1 : pointSliceCheck 0 595 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4Slice2 : pointSliceCheck 0 595 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4Slice3 : pointSliceCheck 0 595 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4Slice4 : pointSliceCheck 0 595 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4Slice5 : pointSliceCheck 0 595 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4Slice6 : pointSliceCheck 0 595 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4Slice7 : pointSliceCheck 0 595 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4Slice8 : pointSliceCheck 0 595 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4Slice9 : pointSliceCheck 0 595 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4Slice10 : pointSliceCheck 0 595 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4Slice11 : pointSliceCheck 0 595 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4Slice12 : pointSliceCheck 0 595 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4Slice13 : pointSliceCheck 0 595 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4Slice14 : pointSliceCheck 0 595 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4Slice15 : pointSliceCheck 0 595 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4Slice16 : pointSliceCheck 0 595 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4Slice17 : pointSliceCheck 0 595 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4Slice18 : pointSliceCheck 0 595 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4Slice19 : pointSliceCheck 0 595 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4Slice20 : pointSliceCheck 0 595 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4Slice21 : pointSliceCheck 0 595 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4Slice22 : pointSliceCheck 0 595 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4Slice23 : pointSliceCheck 0 595 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4Slice24 : pointSliceCheck 0 595 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4Slice25 : pointSliceCheck 0 595 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4Slice26 : pointSliceCheck 0 595 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4Slice27 : pointSliceCheck 0 595 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4Slice28 : pointSliceCheck 0 595 28 := by
  decide +kernel

public theorem point4 : residualCheck 4 := by
  apply ofPointSlices 0 595
  intro c
  fin_cases c
  · exact point4Slice0
  · exact point4Slice1
  · exact point4Slice2
  · exact point4Slice3
  · exact point4Slice4
  · exact point4Slice5
  · exact point4Slice6
  · exact point4Slice7
  · exact point4Slice8
  · exact point4Slice9
  · exact point4Slice10
  · exact point4Slice11
  · exact point4Slice12
  · exact point4Slice13
  · exact point4Slice14
  · exact point4Slice15
  · exact point4Slice16
  · exact point4Slice17
  · exact point4Slice18
  · exact point4Slice19
  · exact point4Slice20
  · exact point4Slice21
  · exact point4Slice22
  · exact point4Slice23
  · exact point4Slice24
  · exact point4Slice25
  · exact point4Slice26
  · exact point4Slice27
  · exact point4Slice28

end Rudvalis.OrderCertificate.ForwardReduction.Part1Residual.Residual0Checks
