module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0ResidualSlices
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-2 residual group 2, transitions 144–149

Check each prescribed permutation identity on 29 slices of 140 points, then
assemble it with `Part0Residual.ofPointSlices`. Separate declarations bound
kernel reduction memory. Source: `OrderLevel0Data` and the transition enumeration
`Part2Residual.target` in `OrderLevel0Part2ResidualReduction`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part2Residual.Residual2Checks
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point144Slice0 : Part0Residual.pointSliceCheck 1 2851 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point144Slice1 : Part0Residual.pointSliceCheck 1 2851 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point144Slice2 : Part0Residual.pointSliceCheck 1 2851 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point144Slice3 : Part0Residual.pointSliceCheck 1 2851 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point144Slice4 : Part0Residual.pointSliceCheck 1 2851 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point144Slice5 : Part0Residual.pointSliceCheck 1 2851 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point144Slice6 : Part0Residual.pointSliceCheck 1 2851 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point144Slice7 : Part0Residual.pointSliceCheck 1 2851 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point144Slice8 : Part0Residual.pointSliceCheck 1 2851 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point144Slice9 : Part0Residual.pointSliceCheck 1 2851 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point144Slice10 : Part0Residual.pointSliceCheck 1 2851 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point144Slice11 : Part0Residual.pointSliceCheck 1 2851 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point144Slice12 : Part0Residual.pointSliceCheck 1 2851 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point144Slice13 : Part0Residual.pointSliceCheck 1 2851 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point144Slice14 : Part0Residual.pointSliceCheck 1 2851 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point144Slice15 : Part0Residual.pointSliceCheck 1 2851 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point144Slice16 : Part0Residual.pointSliceCheck 1 2851 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point144Slice17 : Part0Residual.pointSliceCheck 1 2851 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point144Slice18 : Part0Residual.pointSliceCheck 1 2851 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point144Slice19 : Part0Residual.pointSliceCheck 1 2851 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point144Slice20 : Part0Residual.pointSliceCheck 1 2851 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point144Slice21 : Part0Residual.pointSliceCheck 1 2851 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point144Slice22 : Part0Residual.pointSliceCheck 1 2851 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point144Slice23 : Part0Residual.pointSliceCheck 1 2851 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point144Slice24 : Part0Residual.pointSliceCheck 1 2851 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point144Slice25 : Part0Residual.pointSliceCheck 1 2851 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point144Slice26 : Part0Residual.pointSliceCheck 1 2851 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point144Slice27 : Part0Residual.pointSliceCheck 1 2851 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point144Slice28 : Part0Residual.pointSliceCheck 1 2851 28 := by
  decide +kernel

public theorem point144 : stepCheck 1 2851 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point144Slice0
  · exact point144Slice1
  · exact point144Slice2
  · exact point144Slice3
  · exact point144Slice4
  · exact point144Slice5
  · exact point144Slice6
  · exact point144Slice7
  · exact point144Slice8
  · exact point144Slice9
  · exact point144Slice10
  · exact point144Slice11
  · exact point144Slice12
  · exact point144Slice13
  · exact point144Slice14
  · exact point144Slice15
  · exact point144Slice16
  · exact point144Slice17
  · exact point144Slice18
  · exact point144Slice19
  · exact point144Slice20
  · exact point144Slice21
  · exact point144Slice22
  · exact point144Slice23
  · exact point144Slice24
  · exact point144Slice25
  · exact point144Slice26
  · exact point144Slice27
  · exact point144Slice28

set_option maxHeartbeats 1600000 in
private theorem point145Slice0 : Part0Residual.pointSliceCheck 1 2852 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point145Slice1 : Part0Residual.pointSliceCheck 1 2852 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point145Slice2 : Part0Residual.pointSliceCheck 1 2852 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point145Slice3 : Part0Residual.pointSliceCheck 1 2852 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point145Slice4 : Part0Residual.pointSliceCheck 1 2852 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point145Slice5 : Part0Residual.pointSliceCheck 1 2852 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point145Slice6 : Part0Residual.pointSliceCheck 1 2852 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point145Slice7 : Part0Residual.pointSliceCheck 1 2852 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point145Slice8 : Part0Residual.pointSliceCheck 1 2852 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point145Slice9 : Part0Residual.pointSliceCheck 1 2852 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point145Slice10 : Part0Residual.pointSliceCheck 1 2852 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point145Slice11 : Part0Residual.pointSliceCheck 1 2852 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point145Slice12 : Part0Residual.pointSliceCheck 1 2852 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point145Slice13 : Part0Residual.pointSliceCheck 1 2852 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point145Slice14 : Part0Residual.pointSliceCheck 1 2852 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point145Slice15 : Part0Residual.pointSliceCheck 1 2852 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point145Slice16 : Part0Residual.pointSliceCheck 1 2852 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point145Slice17 : Part0Residual.pointSliceCheck 1 2852 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point145Slice18 : Part0Residual.pointSliceCheck 1 2852 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point145Slice19 : Part0Residual.pointSliceCheck 1 2852 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point145Slice20 : Part0Residual.pointSliceCheck 1 2852 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point145Slice21 : Part0Residual.pointSliceCheck 1 2852 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point145Slice22 : Part0Residual.pointSliceCheck 1 2852 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point145Slice23 : Part0Residual.pointSliceCheck 1 2852 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point145Slice24 : Part0Residual.pointSliceCheck 1 2852 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point145Slice25 : Part0Residual.pointSliceCheck 1 2852 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point145Slice26 : Part0Residual.pointSliceCheck 1 2852 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point145Slice27 : Part0Residual.pointSliceCheck 1 2852 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point145Slice28 : Part0Residual.pointSliceCheck 1 2852 28 := by
  decide +kernel

public theorem point145 : stepCheck 1 2852 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point145Slice0
  · exact point145Slice1
  · exact point145Slice2
  · exact point145Slice3
  · exact point145Slice4
  · exact point145Slice5
  · exact point145Slice6
  · exact point145Slice7
  · exact point145Slice8
  · exact point145Slice9
  · exact point145Slice10
  · exact point145Slice11
  · exact point145Slice12
  · exact point145Slice13
  · exact point145Slice14
  · exact point145Slice15
  · exact point145Slice16
  · exact point145Slice17
  · exact point145Slice18
  · exact point145Slice19
  · exact point145Slice20
  · exact point145Slice21
  · exact point145Slice22
  · exact point145Slice23
  · exact point145Slice24
  · exact point145Slice25
  · exact point145Slice26
  · exact point145Slice27
  · exact point145Slice28

set_option maxHeartbeats 1600000 in
private theorem point146Slice0 : Part0Residual.pointSliceCheck 1 2858 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point146Slice1 : Part0Residual.pointSliceCheck 1 2858 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point146Slice2 : Part0Residual.pointSliceCheck 1 2858 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point146Slice3 : Part0Residual.pointSliceCheck 1 2858 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point146Slice4 : Part0Residual.pointSliceCheck 1 2858 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point146Slice5 : Part0Residual.pointSliceCheck 1 2858 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point146Slice6 : Part0Residual.pointSliceCheck 1 2858 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point146Slice7 : Part0Residual.pointSliceCheck 1 2858 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point146Slice8 : Part0Residual.pointSliceCheck 1 2858 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point146Slice9 : Part0Residual.pointSliceCheck 1 2858 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point146Slice10 : Part0Residual.pointSliceCheck 1 2858 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point146Slice11 : Part0Residual.pointSliceCheck 1 2858 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point146Slice12 : Part0Residual.pointSliceCheck 1 2858 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point146Slice13 : Part0Residual.pointSliceCheck 1 2858 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point146Slice14 : Part0Residual.pointSliceCheck 1 2858 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point146Slice15 : Part0Residual.pointSliceCheck 1 2858 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point146Slice16 : Part0Residual.pointSliceCheck 1 2858 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point146Slice17 : Part0Residual.pointSliceCheck 1 2858 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point146Slice18 : Part0Residual.pointSliceCheck 1 2858 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point146Slice19 : Part0Residual.pointSliceCheck 1 2858 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point146Slice20 : Part0Residual.pointSliceCheck 1 2858 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point146Slice21 : Part0Residual.pointSliceCheck 1 2858 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point146Slice22 : Part0Residual.pointSliceCheck 1 2858 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point146Slice23 : Part0Residual.pointSliceCheck 1 2858 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point146Slice24 : Part0Residual.pointSliceCheck 1 2858 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point146Slice25 : Part0Residual.pointSliceCheck 1 2858 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point146Slice26 : Part0Residual.pointSliceCheck 1 2858 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point146Slice27 : Part0Residual.pointSliceCheck 1 2858 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point146Slice28 : Part0Residual.pointSliceCheck 1 2858 28 := by
  decide +kernel

public theorem point146 : stepCheck 1 2858 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point146Slice0
  · exact point146Slice1
  · exact point146Slice2
  · exact point146Slice3
  · exact point146Slice4
  · exact point146Slice5
  · exact point146Slice6
  · exact point146Slice7
  · exact point146Slice8
  · exact point146Slice9
  · exact point146Slice10
  · exact point146Slice11
  · exact point146Slice12
  · exact point146Slice13
  · exact point146Slice14
  · exact point146Slice15
  · exact point146Slice16
  · exact point146Slice17
  · exact point146Slice18
  · exact point146Slice19
  · exact point146Slice20
  · exact point146Slice21
  · exact point146Slice22
  · exact point146Slice23
  · exact point146Slice24
  · exact point146Slice25
  · exact point146Slice26
  · exact point146Slice27
  · exact point146Slice28

set_option maxHeartbeats 1600000 in
private theorem point147Slice0 : Part0Residual.pointSliceCheck 1 2859 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point147Slice1 : Part0Residual.pointSliceCheck 1 2859 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point147Slice2 : Part0Residual.pointSliceCheck 1 2859 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point147Slice3 : Part0Residual.pointSliceCheck 1 2859 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point147Slice4 : Part0Residual.pointSliceCheck 1 2859 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point147Slice5 : Part0Residual.pointSliceCheck 1 2859 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point147Slice6 : Part0Residual.pointSliceCheck 1 2859 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point147Slice7 : Part0Residual.pointSliceCheck 1 2859 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point147Slice8 : Part0Residual.pointSliceCheck 1 2859 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point147Slice9 : Part0Residual.pointSliceCheck 1 2859 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point147Slice10 : Part0Residual.pointSliceCheck 1 2859 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point147Slice11 : Part0Residual.pointSliceCheck 1 2859 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point147Slice12 : Part0Residual.pointSliceCheck 1 2859 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point147Slice13 : Part0Residual.pointSliceCheck 1 2859 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point147Slice14 : Part0Residual.pointSliceCheck 1 2859 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point147Slice15 : Part0Residual.pointSliceCheck 1 2859 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point147Slice16 : Part0Residual.pointSliceCheck 1 2859 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point147Slice17 : Part0Residual.pointSliceCheck 1 2859 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point147Slice18 : Part0Residual.pointSliceCheck 1 2859 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point147Slice19 : Part0Residual.pointSliceCheck 1 2859 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point147Slice20 : Part0Residual.pointSliceCheck 1 2859 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point147Slice21 : Part0Residual.pointSliceCheck 1 2859 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point147Slice22 : Part0Residual.pointSliceCheck 1 2859 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point147Slice23 : Part0Residual.pointSliceCheck 1 2859 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point147Slice24 : Part0Residual.pointSliceCheck 1 2859 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point147Slice25 : Part0Residual.pointSliceCheck 1 2859 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point147Slice26 : Part0Residual.pointSliceCheck 1 2859 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point147Slice27 : Part0Residual.pointSliceCheck 1 2859 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point147Slice28 : Part0Residual.pointSliceCheck 1 2859 28 := by
  decide +kernel

public theorem point147 : stepCheck 1 2859 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point147Slice0
  · exact point147Slice1
  · exact point147Slice2
  · exact point147Slice3
  · exact point147Slice4
  · exact point147Slice5
  · exact point147Slice6
  · exact point147Slice7
  · exact point147Slice8
  · exact point147Slice9
  · exact point147Slice10
  · exact point147Slice11
  · exact point147Slice12
  · exact point147Slice13
  · exact point147Slice14
  · exact point147Slice15
  · exact point147Slice16
  · exact point147Slice17
  · exact point147Slice18
  · exact point147Slice19
  · exact point147Slice20
  · exact point147Slice21
  · exact point147Slice22
  · exact point147Slice23
  · exact point147Slice24
  · exact point147Slice25
  · exact point147Slice26
  · exact point147Slice27
  · exact point147Slice28

set_option maxHeartbeats 1600000 in
private theorem point148Slice0 : Part0Residual.pointSliceCheck 0 2982 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point148Slice1 : Part0Residual.pointSliceCheck 0 2982 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point148Slice2 : Part0Residual.pointSliceCheck 0 2982 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point148Slice3 : Part0Residual.pointSliceCheck 0 2982 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point148Slice4 : Part0Residual.pointSliceCheck 0 2982 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point148Slice5 : Part0Residual.pointSliceCheck 0 2982 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point148Slice6 : Part0Residual.pointSliceCheck 0 2982 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point148Slice7 : Part0Residual.pointSliceCheck 0 2982 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point148Slice8 : Part0Residual.pointSliceCheck 0 2982 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point148Slice9 : Part0Residual.pointSliceCheck 0 2982 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point148Slice10 : Part0Residual.pointSliceCheck 0 2982 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point148Slice11 : Part0Residual.pointSliceCheck 0 2982 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point148Slice12 : Part0Residual.pointSliceCheck 0 2982 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point148Slice13 : Part0Residual.pointSliceCheck 0 2982 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point148Slice14 : Part0Residual.pointSliceCheck 0 2982 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point148Slice15 : Part0Residual.pointSliceCheck 0 2982 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point148Slice16 : Part0Residual.pointSliceCheck 0 2982 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point148Slice17 : Part0Residual.pointSliceCheck 0 2982 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point148Slice18 : Part0Residual.pointSliceCheck 0 2982 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point148Slice19 : Part0Residual.pointSliceCheck 0 2982 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point148Slice20 : Part0Residual.pointSliceCheck 0 2982 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point148Slice21 : Part0Residual.pointSliceCheck 0 2982 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point148Slice22 : Part0Residual.pointSliceCheck 0 2982 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point148Slice23 : Part0Residual.pointSliceCheck 0 2982 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point148Slice24 : Part0Residual.pointSliceCheck 0 2982 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point148Slice25 : Part0Residual.pointSliceCheck 0 2982 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point148Slice26 : Part0Residual.pointSliceCheck 0 2982 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point148Slice27 : Part0Residual.pointSliceCheck 0 2982 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point148Slice28 : Part0Residual.pointSliceCheck 0 2982 28 := by
  decide +kernel

public theorem point148 : stepCheck 0 2982 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point148Slice0
  · exact point148Slice1
  · exact point148Slice2
  · exact point148Slice3
  · exact point148Slice4
  · exact point148Slice5
  · exact point148Slice6
  · exact point148Slice7
  · exact point148Slice8
  · exact point148Slice9
  · exact point148Slice10
  · exact point148Slice11
  · exact point148Slice12
  · exact point148Slice13
  · exact point148Slice14
  · exact point148Slice15
  · exact point148Slice16
  · exact point148Slice17
  · exact point148Slice18
  · exact point148Slice19
  · exact point148Slice20
  · exact point148Slice21
  · exact point148Slice22
  · exact point148Slice23
  · exact point148Slice24
  · exact point148Slice25
  · exact point148Slice26
  · exact point148Slice27
  · exact point148Slice28

set_option maxHeartbeats 1600000 in
private theorem point149Slice0 : Part0Residual.pointSliceCheck 0 2983 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point149Slice1 : Part0Residual.pointSliceCheck 0 2983 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point149Slice2 : Part0Residual.pointSliceCheck 0 2983 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point149Slice3 : Part0Residual.pointSliceCheck 0 2983 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point149Slice4 : Part0Residual.pointSliceCheck 0 2983 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point149Slice5 : Part0Residual.pointSliceCheck 0 2983 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point149Slice6 : Part0Residual.pointSliceCheck 0 2983 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point149Slice7 : Part0Residual.pointSliceCheck 0 2983 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point149Slice8 : Part0Residual.pointSliceCheck 0 2983 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point149Slice9 : Part0Residual.pointSliceCheck 0 2983 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point149Slice10 : Part0Residual.pointSliceCheck 0 2983 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point149Slice11 : Part0Residual.pointSliceCheck 0 2983 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point149Slice12 : Part0Residual.pointSliceCheck 0 2983 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point149Slice13 : Part0Residual.pointSliceCheck 0 2983 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point149Slice14 : Part0Residual.pointSliceCheck 0 2983 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point149Slice15 : Part0Residual.pointSliceCheck 0 2983 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point149Slice16 : Part0Residual.pointSliceCheck 0 2983 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point149Slice17 : Part0Residual.pointSliceCheck 0 2983 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point149Slice18 : Part0Residual.pointSliceCheck 0 2983 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point149Slice19 : Part0Residual.pointSliceCheck 0 2983 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point149Slice20 : Part0Residual.pointSliceCheck 0 2983 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point149Slice21 : Part0Residual.pointSliceCheck 0 2983 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point149Slice22 : Part0Residual.pointSliceCheck 0 2983 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point149Slice23 : Part0Residual.pointSliceCheck 0 2983 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point149Slice24 : Part0Residual.pointSliceCheck 0 2983 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point149Slice25 : Part0Residual.pointSliceCheck 0 2983 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point149Slice26 : Part0Residual.pointSliceCheck 0 2983 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point149Slice27 : Part0Residual.pointSliceCheck 0 2983 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point149Slice28 : Part0Residual.pointSliceCheck 0 2983 28 := by
  decide +kernel

public theorem point149 : stepCheck 0 2983 := by
  apply Part0Residual.ofPointSlices
  intro c
  fin_cases c
  · exact point149Slice0
  · exact point149Slice1
  · exact point149Slice2
  · exact point149Slice3
  · exact point149Slice4
  · exact point149Slice5
  · exact point149Slice6
  · exact point149Slice7
  · exact point149Slice8
  · exact point149Slice9
  · exact point149Slice10
  · exact point149Slice11
  · exact point149Slice12
  · exact point149Slice13
  · exact point149Slice14
  · exact point149Slice15
  · exact point149Slice16
  · exact point149Slice17
  · exact point149Slice18
  · exact point149Slice19
  · exact point149Slice20
  · exact point149Slice21
  · exact point149Slice22
  · exact point149Slice23
  · exact point149Slice24
  · exact point149Slice25
  · exact point149Slice26
  · exact point149Slice27
  · exact point149Slice28

end Rudvalis.OrderCertificate.ForwardReduction.Part2Residual.Residual2Checks
