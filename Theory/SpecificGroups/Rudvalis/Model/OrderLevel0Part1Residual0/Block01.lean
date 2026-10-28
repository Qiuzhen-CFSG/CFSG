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
private theorem point5Slice0 : pointSliceCheck 1 581 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5Slice1 : pointSliceCheck 1 581 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5Slice2 : pointSliceCheck 1 581 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5Slice3 : pointSliceCheck 1 581 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5Slice4 : pointSliceCheck 1 581 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5Slice5 : pointSliceCheck 1 581 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5Slice6 : pointSliceCheck 1 581 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5Slice7 : pointSliceCheck 1 581 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5Slice8 : pointSliceCheck 1 581 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5Slice9 : pointSliceCheck 1 581 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5Slice10 : pointSliceCheck 1 581 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5Slice11 : pointSliceCheck 1 581 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5Slice12 : pointSliceCheck 1 581 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5Slice13 : pointSliceCheck 1 581 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5Slice14 : pointSliceCheck 1 581 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5Slice15 : pointSliceCheck 1 581 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5Slice16 : pointSliceCheck 1 581 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5Slice17 : pointSliceCheck 1 581 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5Slice18 : pointSliceCheck 1 581 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5Slice19 : pointSliceCheck 1 581 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5Slice20 : pointSliceCheck 1 581 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5Slice21 : pointSliceCheck 1 581 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5Slice22 : pointSliceCheck 1 581 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5Slice23 : pointSliceCheck 1 581 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5Slice24 : pointSliceCheck 1 581 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5Slice25 : pointSliceCheck 1 581 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5Slice26 : pointSliceCheck 1 581 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5Slice27 : pointSliceCheck 1 581 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5Slice28 : pointSliceCheck 1 581 28 := by
  decide +kernel

public theorem point5 : residualCheck 5 := by
  apply ofPointSlices 1 581
  intro c
  fin_cases c
  · exact point5Slice0
  · exact point5Slice1
  · exact point5Slice2
  · exact point5Slice3
  · exact point5Slice4
  · exact point5Slice5
  · exact point5Slice6
  · exact point5Slice7
  · exact point5Slice8
  · exact point5Slice9
  · exact point5Slice10
  · exact point5Slice11
  · exact point5Slice12
  · exact point5Slice13
  · exact point5Slice14
  · exact point5Slice15
  · exact point5Slice16
  · exact point5Slice17
  · exact point5Slice18
  · exact point5Slice19
  · exact point5Slice20
  · exact point5Slice21
  · exact point5Slice22
  · exact point5Slice23
  · exact point5Slice24
  · exact point5Slice25
  · exact point5Slice26
  · exact point5Slice27
  · exact point5Slice28

set_option maxHeartbeats 1600000 in
private theorem point6Slice0 : pointSliceCheck 0 728 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6Slice1 : pointSliceCheck 0 728 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6Slice2 : pointSliceCheck 0 728 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6Slice3 : pointSliceCheck 0 728 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6Slice4 : pointSliceCheck 0 728 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6Slice5 : pointSliceCheck 0 728 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6Slice6 : pointSliceCheck 0 728 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6Slice7 : pointSliceCheck 0 728 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6Slice8 : pointSliceCheck 0 728 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6Slice9 : pointSliceCheck 0 728 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6Slice10 : pointSliceCheck 0 728 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6Slice11 : pointSliceCheck 0 728 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6Slice12 : pointSliceCheck 0 728 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6Slice13 : pointSliceCheck 0 728 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6Slice14 : pointSliceCheck 0 728 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6Slice15 : pointSliceCheck 0 728 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6Slice16 : pointSliceCheck 0 728 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6Slice17 : pointSliceCheck 0 728 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6Slice18 : pointSliceCheck 0 728 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6Slice19 : pointSliceCheck 0 728 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6Slice20 : pointSliceCheck 0 728 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6Slice21 : pointSliceCheck 0 728 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6Slice22 : pointSliceCheck 0 728 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6Slice23 : pointSliceCheck 0 728 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6Slice24 : pointSliceCheck 0 728 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6Slice25 : pointSliceCheck 0 728 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6Slice26 : pointSliceCheck 0 728 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6Slice27 : pointSliceCheck 0 728 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6Slice28 : pointSliceCheck 0 728 28 := by
  decide +kernel

public theorem point6 : residualCheck 6 := by
  apply ofPointSlices 0 728
  intro c
  fin_cases c
  · exact point6Slice0
  · exact point6Slice1
  · exact point6Slice2
  · exact point6Slice3
  · exact point6Slice4
  · exact point6Slice5
  · exact point6Slice6
  · exact point6Slice7
  · exact point6Slice8
  · exact point6Slice9
  · exact point6Slice10
  · exact point6Slice11
  · exact point6Slice12
  · exact point6Slice13
  · exact point6Slice14
  · exact point6Slice15
  · exact point6Slice16
  · exact point6Slice17
  · exact point6Slice18
  · exact point6Slice19
  · exact point6Slice20
  · exact point6Slice21
  · exact point6Slice22
  · exact point6Slice23
  · exact point6Slice24
  · exact point6Slice25
  · exact point6Slice26
  · exact point6Slice27
  · exact point6Slice28

set_option maxHeartbeats 1600000 in
private theorem point7Slice0 : pointSliceCheck 1 736 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7Slice1 : pointSliceCheck 1 736 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7Slice2 : pointSliceCheck 1 736 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7Slice3 : pointSliceCheck 1 736 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7Slice4 : pointSliceCheck 1 736 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7Slice5 : pointSliceCheck 1 736 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7Slice6 : pointSliceCheck 1 736 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7Slice7 : pointSliceCheck 1 736 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7Slice8 : pointSliceCheck 1 736 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7Slice9 : pointSliceCheck 1 736 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7Slice10 : pointSliceCheck 1 736 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7Slice11 : pointSliceCheck 1 736 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7Slice12 : pointSliceCheck 1 736 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7Slice13 : pointSliceCheck 1 736 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7Slice14 : pointSliceCheck 1 736 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7Slice15 : pointSliceCheck 1 736 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7Slice16 : pointSliceCheck 1 736 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7Slice17 : pointSliceCheck 1 736 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7Slice18 : pointSliceCheck 1 736 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7Slice19 : pointSliceCheck 1 736 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7Slice20 : pointSliceCheck 1 736 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7Slice21 : pointSliceCheck 1 736 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7Slice22 : pointSliceCheck 1 736 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7Slice23 : pointSliceCheck 1 736 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7Slice24 : pointSliceCheck 1 736 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7Slice25 : pointSliceCheck 1 736 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7Slice26 : pointSliceCheck 1 736 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7Slice27 : pointSliceCheck 1 736 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7Slice28 : pointSliceCheck 1 736 28 := by
  decide +kernel

public theorem point7 : residualCheck 7 := by
  apply ofPointSlices 1 736
  intro c
  fin_cases c
  · exact point7Slice0
  · exact point7Slice1
  · exact point7Slice2
  · exact point7Slice3
  · exact point7Slice4
  · exact point7Slice5
  · exact point7Slice6
  · exact point7Slice7
  · exact point7Slice8
  · exact point7Slice9
  · exact point7Slice10
  · exact point7Slice11
  · exact point7Slice12
  · exact point7Slice13
  · exact point7Slice14
  · exact point7Slice15
  · exact point7Slice16
  · exact point7Slice17
  · exact point7Slice18
  · exact point7Slice19
  · exact point7Slice20
  · exact point7Slice21
  · exact point7Slice22
  · exact point7Slice23
  · exact point7Slice24
  · exact point7Slice25
  · exact point7Slice26
  · exact point7Slice27
  · exact point7Slice28

set_option maxHeartbeats 1600000 in
private theorem point8Slice0 : pointSliceCheck 0 860 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8Slice1 : pointSliceCheck 0 860 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8Slice2 : pointSliceCheck 0 860 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8Slice3 : pointSliceCheck 0 860 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8Slice4 : pointSliceCheck 0 860 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8Slice5 : pointSliceCheck 0 860 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8Slice6 : pointSliceCheck 0 860 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8Slice7 : pointSliceCheck 0 860 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8Slice8 : pointSliceCheck 0 860 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8Slice9 : pointSliceCheck 0 860 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8Slice10 : pointSliceCheck 0 860 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8Slice11 : pointSliceCheck 0 860 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8Slice12 : pointSliceCheck 0 860 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8Slice13 : pointSliceCheck 0 860 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8Slice14 : pointSliceCheck 0 860 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8Slice15 : pointSliceCheck 0 860 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8Slice16 : pointSliceCheck 0 860 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8Slice17 : pointSliceCheck 0 860 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8Slice18 : pointSliceCheck 0 860 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8Slice19 : pointSliceCheck 0 860 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8Slice20 : pointSliceCheck 0 860 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8Slice21 : pointSliceCheck 0 860 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8Slice22 : pointSliceCheck 0 860 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8Slice23 : pointSliceCheck 0 860 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8Slice24 : pointSliceCheck 0 860 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8Slice25 : pointSliceCheck 0 860 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8Slice26 : pointSliceCheck 0 860 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8Slice27 : pointSliceCheck 0 860 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8Slice28 : pointSliceCheck 0 860 28 := by
  decide +kernel

public theorem point8 : residualCheck 8 := by
  apply ofPointSlices 0 860
  intro c
  fin_cases c
  · exact point8Slice0
  · exact point8Slice1
  · exact point8Slice2
  · exact point8Slice3
  · exact point8Slice4
  · exact point8Slice5
  · exact point8Slice6
  · exact point8Slice7
  · exact point8Slice8
  · exact point8Slice9
  · exact point8Slice10
  · exact point8Slice11
  · exact point8Slice12
  · exact point8Slice13
  · exact point8Slice14
  · exact point8Slice15
  · exact point8Slice16
  · exact point8Slice17
  · exact point8Slice18
  · exact point8Slice19
  · exact point8Slice20
  · exact point8Slice21
  · exact point8Slice22
  · exact point8Slice23
  · exact point8Slice24
  · exact point8Slice25
  · exact point8Slice26
  · exact point8Slice27
  · exact point8Slice28

set_option maxHeartbeats 1600000 in
private theorem point9Slice0 : pointSliceCheck 0 878 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9Slice1 : pointSliceCheck 0 878 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9Slice2 : pointSliceCheck 0 878 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9Slice3 : pointSliceCheck 0 878 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9Slice4 : pointSliceCheck 0 878 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9Slice5 : pointSliceCheck 0 878 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9Slice6 : pointSliceCheck 0 878 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9Slice7 : pointSliceCheck 0 878 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9Slice8 : pointSliceCheck 0 878 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9Slice9 : pointSliceCheck 0 878 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9Slice10 : pointSliceCheck 0 878 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9Slice11 : pointSliceCheck 0 878 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9Slice12 : pointSliceCheck 0 878 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9Slice13 : pointSliceCheck 0 878 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9Slice14 : pointSliceCheck 0 878 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9Slice15 : pointSliceCheck 0 878 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9Slice16 : pointSliceCheck 0 878 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9Slice17 : pointSliceCheck 0 878 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9Slice18 : pointSliceCheck 0 878 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9Slice19 : pointSliceCheck 0 878 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9Slice20 : pointSliceCheck 0 878 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9Slice21 : pointSliceCheck 0 878 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9Slice22 : pointSliceCheck 0 878 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9Slice23 : pointSliceCheck 0 878 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9Slice24 : pointSliceCheck 0 878 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9Slice25 : pointSliceCheck 0 878 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9Slice26 : pointSliceCheck 0 878 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9Slice27 : pointSliceCheck 0 878 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9Slice28 : pointSliceCheck 0 878 28 := by
  decide +kernel

public theorem point9 : residualCheck 9 := by
  apply ofPointSlices 0 878
  intro c
  fin_cases c
  · exact point9Slice0
  · exact point9Slice1
  · exact point9Slice2
  · exact point9Slice3
  · exact point9Slice4
  · exact point9Slice5
  · exact point9Slice6
  · exact point9Slice7
  · exact point9Slice8
  · exact point9Slice9
  · exact point9Slice10
  · exact point9Slice11
  · exact point9Slice12
  · exact point9Slice13
  · exact point9Slice14
  · exact point9Slice15
  · exact point9Slice16
  · exact point9Slice17
  · exact point9Slice18
  · exact point9Slice19
  · exact point9Slice20
  · exact point9Slice21
  · exact point9Slice22
  · exact point9Slice23
  · exact point9Slice24
  · exact point9Slice25
  · exact point9Slice26
  · exact point9Slice27
  · exact point9Slice28

end Rudvalis.OrderCertificate.ForwardReduction.Part1Residual.Residual0Checks
