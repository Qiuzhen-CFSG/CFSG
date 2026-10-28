module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0ResidualSlices
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-0 residual group 0, transitions 10–14

The prescribed permutation identities are checked on 29 slices of 140 points
and then assembled by `ofPointSlices`. Separate slice declarations bound kernel
reduction memory. Source: the witnesses in `OrderLevel0Data` and the exact
transition enumeration `Part0Residual.target` in `OrderLevel0Part0ResidualReduction`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual0Checks
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point10Slice0 : pointSliceCheck 0 981 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10Slice1 : pointSliceCheck 0 981 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10Slice2 : pointSliceCheck 0 981 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10Slice3 : pointSliceCheck 0 981 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10Slice4 : pointSliceCheck 0 981 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10Slice5 : pointSliceCheck 0 981 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10Slice6 : pointSliceCheck 0 981 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10Slice7 : pointSliceCheck 0 981 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10Slice8 : pointSliceCheck 0 981 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10Slice9 : pointSliceCheck 0 981 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10Slice10 : pointSliceCheck 0 981 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10Slice11 : pointSliceCheck 0 981 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10Slice12 : pointSliceCheck 0 981 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10Slice13 : pointSliceCheck 0 981 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10Slice14 : pointSliceCheck 0 981 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10Slice15 : pointSliceCheck 0 981 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10Slice16 : pointSliceCheck 0 981 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10Slice17 : pointSliceCheck 0 981 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10Slice18 : pointSliceCheck 0 981 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10Slice19 : pointSliceCheck 0 981 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10Slice20 : pointSliceCheck 0 981 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10Slice21 : pointSliceCheck 0 981 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10Slice22 : pointSliceCheck 0 981 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10Slice23 : pointSliceCheck 0 981 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10Slice24 : pointSliceCheck 0 981 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10Slice25 : pointSliceCheck 0 981 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10Slice26 : pointSliceCheck 0 981 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10Slice27 : pointSliceCheck 0 981 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10Slice28 : pointSliceCheck 0 981 28 := by
  decide +kernel

public theorem point10 : residualCheck 10 := by
  apply ofPointSlices 0 981
  intro c
  fin_cases c
  · exact point10Slice0
  · exact point10Slice1
  · exact point10Slice2
  · exact point10Slice3
  · exact point10Slice4
  · exact point10Slice5
  · exact point10Slice6
  · exact point10Slice7
  · exact point10Slice8
  · exact point10Slice9
  · exact point10Slice10
  · exact point10Slice11
  · exact point10Slice12
  · exact point10Slice13
  · exact point10Slice14
  · exact point10Slice15
  · exact point10Slice16
  · exact point10Slice17
  · exact point10Slice18
  · exact point10Slice19
  · exact point10Slice20
  · exact point10Slice21
  · exact point10Slice22
  · exact point10Slice23
  · exact point10Slice24
  · exact point10Slice25
  · exact point10Slice26
  · exact point10Slice27
  · exact point10Slice28

set_option maxHeartbeats 1600000 in
private theorem point11Slice0 : pointSliceCheck 0 987 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11Slice1 : pointSliceCheck 0 987 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11Slice2 : pointSliceCheck 0 987 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11Slice3 : pointSliceCheck 0 987 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11Slice4 : pointSliceCheck 0 987 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11Slice5 : pointSliceCheck 0 987 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11Slice6 : pointSliceCheck 0 987 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11Slice7 : pointSliceCheck 0 987 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11Slice8 : pointSliceCheck 0 987 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11Slice9 : pointSliceCheck 0 987 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11Slice10 : pointSliceCheck 0 987 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11Slice11 : pointSliceCheck 0 987 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11Slice12 : pointSliceCheck 0 987 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11Slice13 : pointSliceCheck 0 987 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11Slice14 : pointSliceCheck 0 987 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11Slice15 : pointSliceCheck 0 987 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11Slice16 : pointSliceCheck 0 987 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11Slice17 : pointSliceCheck 0 987 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11Slice18 : pointSliceCheck 0 987 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11Slice19 : pointSliceCheck 0 987 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11Slice20 : pointSliceCheck 0 987 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11Slice21 : pointSliceCheck 0 987 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11Slice22 : pointSliceCheck 0 987 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11Slice23 : pointSliceCheck 0 987 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11Slice24 : pointSliceCheck 0 987 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11Slice25 : pointSliceCheck 0 987 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11Slice26 : pointSliceCheck 0 987 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11Slice27 : pointSliceCheck 0 987 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11Slice28 : pointSliceCheck 0 987 28 := by
  decide +kernel

public theorem point11 : residualCheck 11 := by
  apply ofPointSlices 0 987
  intro c
  fin_cases c
  · exact point11Slice0
  · exact point11Slice1
  · exact point11Slice2
  · exact point11Slice3
  · exact point11Slice4
  · exact point11Slice5
  · exact point11Slice6
  · exact point11Slice7
  · exact point11Slice8
  · exact point11Slice9
  · exact point11Slice10
  · exact point11Slice11
  · exact point11Slice12
  · exact point11Slice13
  · exact point11Slice14
  · exact point11Slice15
  · exact point11Slice16
  · exact point11Slice17
  · exact point11Slice18
  · exact point11Slice19
  · exact point11Slice20
  · exact point11Slice21
  · exact point11Slice22
  · exact point11Slice23
  · exact point11Slice24
  · exact point11Slice25
  · exact point11Slice26
  · exact point11Slice27
  · exact point11Slice28

set_option maxHeartbeats 1600000 in
private theorem point12Slice0 : pointSliceCheck 0 989 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12Slice1 : pointSliceCheck 0 989 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12Slice2 : pointSliceCheck 0 989 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12Slice3 : pointSliceCheck 0 989 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12Slice4 : pointSliceCheck 0 989 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12Slice5 : pointSliceCheck 0 989 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12Slice6 : pointSliceCheck 0 989 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12Slice7 : pointSliceCheck 0 989 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12Slice8 : pointSliceCheck 0 989 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12Slice9 : pointSliceCheck 0 989 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12Slice10 : pointSliceCheck 0 989 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12Slice11 : pointSliceCheck 0 989 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12Slice12 : pointSliceCheck 0 989 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12Slice13 : pointSliceCheck 0 989 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12Slice14 : pointSliceCheck 0 989 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12Slice15 : pointSliceCheck 0 989 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12Slice16 : pointSliceCheck 0 989 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12Slice17 : pointSliceCheck 0 989 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12Slice18 : pointSliceCheck 0 989 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12Slice19 : pointSliceCheck 0 989 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12Slice20 : pointSliceCheck 0 989 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12Slice21 : pointSliceCheck 0 989 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12Slice22 : pointSliceCheck 0 989 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12Slice23 : pointSliceCheck 0 989 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12Slice24 : pointSliceCheck 0 989 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12Slice25 : pointSliceCheck 0 989 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12Slice26 : pointSliceCheck 0 989 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12Slice27 : pointSliceCheck 0 989 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12Slice28 : pointSliceCheck 0 989 28 := by
  decide +kernel

public theorem point12 : residualCheck 12 := by
  apply ofPointSlices 0 989
  intro c
  fin_cases c
  · exact point12Slice0
  · exact point12Slice1
  · exact point12Slice2
  · exact point12Slice3
  · exact point12Slice4
  · exact point12Slice5
  · exact point12Slice6
  · exact point12Slice7
  · exact point12Slice8
  · exact point12Slice9
  · exact point12Slice10
  · exact point12Slice11
  · exact point12Slice12
  · exact point12Slice13
  · exact point12Slice14
  · exact point12Slice15
  · exact point12Slice16
  · exact point12Slice17
  · exact point12Slice18
  · exact point12Slice19
  · exact point12Slice20
  · exact point12Slice21
  · exact point12Slice22
  · exact point12Slice23
  · exact point12Slice24
  · exact point12Slice25
  · exact point12Slice26
  · exact point12Slice27
  · exact point12Slice28

set_option maxHeartbeats 1600000 in
private theorem point13Slice0 : pointSliceCheck 0 994 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13Slice1 : pointSliceCheck 0 994 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13Slice2 : pointSliceCheck 0 994 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13Slice3 : pointSliceCheck 0 994 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13Slice4 : pointSliceCheck 0 994 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13Slice5 : pointSliceCheck 0 994 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13Slice6 : pointSliceCheck 0 994 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13Slice7 : pointSliceCheck 0 994 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13Slice8 : pointSliceCheck 0 994 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13Slice9 : pointSliceCheck 0 994 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13Slice10 : pointSliceCheck 0 994 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13Slice11 : pointSliceCheck 0 994 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13Slice12 : pointSliceCheck 0 994 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13Slice13 : pointSliceCheck 0 994 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13Slice14 : pointSliceCheck 0 994 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13Slice15 : pointSliceCheck 0 994 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13Slice16 : pointSliceCheck 0 994 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13Slice17 : pointSliceCheck 0 994 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13Slice18 : pointSliceCheck 0 994 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13Slice19 : pointSliceCheck 0 994 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13Slice20 : pointSliceCheck 0 994 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13Slice21 : pointSliceCheck 0 994 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13Slice22 : pointSliceCheck 0 994 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13Slice23 : pointSliceCheck 0 994 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13Slice24 : pointSliceCheck 0 994 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13Slice25 : pointSliceCheck 0 994 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13Slice26 : pointSliceCheck 0 994 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13Slice27 : pointSliceCheck 0 994 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13Slice28 : pointSliceCheck 0 994 28 := by
  decide +kernel

public theorem point13 : residualCheck 13 := by
  apply ofPointSlices 0 994
  intro c
  fin_cases c
  · exact point13Slice0
  · exact point13Slice1
  · exact point13Slice2
  · exact point13Slice3
  · exact point13Slice4
  · exact point13Slice5
  · exact point13Slice6
  · exact point13Slice7
  · exact point13Slice8
  · exact point13Slice9
  · exact point13Slice10
  · exact point13Slice11
  · exact point13Slice12
  · exact point13Slice13
  · exact point13Slice14
  · exact point13Slice15
  · exact point13Slice16
  · exact point13Slice17
  · exact point13Slice18
  · exact point13Slice19
  · exact point13Slice20
  · exact point13Slice21
  · exact point13Slice22
  · exact point13Slice23
  · exact point13Slice24
  · exact point13Slice25
  · exact point13Slice26
  · exact point13Slice27
  · exact point13Slice28

set_option maxHeartbeats 1600000 in
private theorem point14Slice0 : pointSliceCheck 1 994 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14Slice1 : pointSliceCheck 1 994 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14Slice2 : pointSliceCheck 1 994 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14Slice3 : pointSliceCheck 1 994 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14Slice4 : pointSliceCheck 1 994 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14Slice5 : pointSliceCheck 1 994 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14Slice6 : pointSliceCheck 1 994 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14Slice7 : pointSliceCheck 1 994 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14Slice8 : pointSliceCheck 1 994 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14Slice9 : pointSliceCheck 1 994 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14Slice10 : pointSliceCheck 1 994 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14Slice11 : pointSliceCheck 1 994 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14Slice12 : pointSliceCheck 1 994 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14Slice13 : pointSliceCheck 1 994 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14Slice14 : pointSliceCheck 1 994 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14Slice15 : pointSliceCheck 1 994 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14Slice16 : pointSliceCheck 1 994 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14Slice17 : pointSliceCheck 1 994 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14Slice18 : pointSliceCheck 1 994 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14Slice19 : pointSliceCheck 1 994 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14Slice20 : pointSliceCheck 1 994 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14Slice21 : pointSliceCheck 1 994 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14Slice22 : pointSliceCheck 1 994 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14Slice23 : pointSliceCheck 1 994 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14Slice24 : pointSliceCheck 1 994 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14Slice25 : pointSliceCheck 1 994 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14Slice26 : pointSliceCheck 1 994 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14Slice27 : pointSliceCheck 1 994 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14Slice28 : pointSliceCheck 1 994 28 := by
  decide +kernel

public theorem point14 : residualCheck 14 := by
  apply ofPointSlices 1 994
  intro c
  fin_cases c
  · exact point14Slice0
  · exact point14Slice1
  · exact point14Slice2
  · exact point14Slice3
  · exact point14Slice4
  · exact point14Slice5
  · exact point14Slice6
  · exact point14Slice7
  · exact point14Slice8
  · exact point14Slice9
  · exact point14Slice10
  · exact point14Slice11
  · exact point14Slice12
  · exact point14Slice13
  · exact point14Slice14
  · exact point14Slice15
  · exact point14Slice16
  · exact point14Slice17
  · exact point14Slice18
  · exact point14Slice19
  · exact point14Slice20
  · exact point14Slice21
  · exact point14Slice22
  · exact point14Slice23
  · exact point14Slice24
  · exact point14Slice25
  · exact point14Slice26
  · exact point14Slice27
  · exact point14Slice28

end Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual0Checks
