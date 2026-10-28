module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0ResidualSlices
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-0 residual group 0, transitions 45–49

The prescribed permutation identities are checked on 29 slices of 140 points
and then assembled by `ofPointSlices`. Separate slice declarations bound kernel
reduction memory. Source: the witnesses in `OrderLevel0Data` and the exact
transition enumeration `Part0Residual.target` in `OrderLevel0Part0ResidualReduction`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual0Checks
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point45Slice0 : pointSliceCheck 0 1691 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point45Slice1 : pointSliceCheck 0 1691 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point45Slice2 : pointSliceCheck 0 1691 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point45Slice3 : pointSliceCheck 0 1691 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point45Slice4 : pointSliceCheck 0 1691 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point45Slice5 : pointSliceCheck 0 1691 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point45Slice6 : pointSliceCheck 0 1691 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point45Slice7 : pointSliceCheck 0 1691 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point45Slice8 : pointSliceCheck 0 1691 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point45Slice9 : pointSliceCheck 0 1691 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point45Slice10 : pointSliceCheck 0 1691 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point45Slice11 : pointSliceCheck 0 1691 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point45Slice12 : pointSliceCheck 0 1691 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point45Slice13 : pointSliceCheck 0 1691 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point45Slice14 : pointSliceCheck 0 1691 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point45Slice15 : pointSliceCheck 0 1691 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point45Slice16 : pointSliceCheck 0 1691 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point45Slice17 : pointSliceCheck 0 1691 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point45Slice18 : pointSliceCheck 0 1691 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point45Slice19 : pointSliceCheck 0 1691 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point45Slice20 : pointSliceCheck 0 1691 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point45Slice21 : pointSliceCheck 0 1691 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point45Slice22 : pointSliceCheck 0 1691 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point45Slice23 : pointSliceCheck 0 1691 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point45Slice24 : pointSliceCheck 0 1691 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point45Slice25 : pointSliceCheck 0 1691 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point45Slice26 : pointSliceCheck 0 1691 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point45Slice27 : pointSliceCheck 0 1691 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point45Slice28 : pointSliceCheck 0 1691 28 := by
  decide +kernel

public theorem point45 : residualCheck 45 := by
  apply ofPointSlices 0 1691
  intro c
  fin_cases c
  · exact point45Slice0
  · exact point45Slice1
  · exact point45Slice2
  · exact point45Slice3
  · exact point45Slice4
  · exact point45Slice5
  · exact point45Slice6
  · exact point45Slice7
  · exact point45Slice8
  · exact point45Slice9
  · exact point45Slice10
  · exact point45Slice11
  · exact point45Slice12
  · exact point45Slice13
  · exact point45Slice14
  · exact point45Slice15
  · exact point45Slice16
  · exact point45Slice17
  · exact point45Slice18
  · exact point45Slice19
  · exact point45Slice20
  · exact point45Slice21
  · exact point45Slice22
  · exact point45Slice23
  · exact point45Slice24
  · exact point45Slice25
  · exact point45Slice26
  · exact point45Slice27
  · exact point45Slice28

set_option maxHeartbeats 1600000 in
private theorem point46Slice0 : pointSliceCheck 0 1694 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point46Slice1 : pointSliceCheck 0 1694 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point46Slice2 : pointSliceCheck 0 1694 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point46Slice3 : pointSliceCheck 0 1694 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point46Slice4 : pointSliceCheck 0 1694 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point46Slice5 : pointSliceCheck 0 1694 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point46Slice6 : pointSliceCheck 0 1694 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point46Slice7 : pointSliceCheck 0 1694 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point46Slice8 : pointSliceCheck 0 1694 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point46Slice9 : pointSliceCheck 0 1694 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point46Slice10 : pointSliceCheck 0 1694 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point46Slice11 : pointSliceCheck 0 1694 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point46Slice12 : pointSliceCheck 0 1694 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point46Slice13 : pointSliceCheck 0 1694 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point46Slice14 : pointSliceCheck 0 1694 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point46Slice15 : pointSliceCheck 0 1694 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point46Slice16 : pointSliceCheck 0 1694 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point46Slice17 : pointSliceCheck 0 1694 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point46Slice18 : pointSliceCheck 0 1694 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point46Slice19 : pointSliceCheck 0 1694 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point46Slice20 : pointSliceCheck 0 1694 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point46Slice21 : pointSliceCheck 0 1694 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point46Slice22 : pointSliceCheck 0 1694 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point46Slice23 : pointSliceCheck 0 1694 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point46Slice24 : pointSliceCheck 0 1694 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point46Slice25 : pointSliceCheck 0 1694 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point46Slice26 : pointSliceCheck 0 1694 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point46Slice27 : pointSliceCheck 0 1694 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point46Slice28 : pointSliceCheck 0 1694 28 := by
  decide +kernel

public theorem point46 : residualCheck 46 := by
  apply ofPointSlices 0 1694
  intro c
  fin_cases c
  · exact point46Slice0
  · exact point46Slice1
  · exact point46Slice2
  · exact point46Slice3
  · exact point46Slice4
  · exact point46Slice5
  · exact point46Slice6
  · exact point46Slice7
  · exact point46Slice8
  · exact point46Slice9
  · exact point46Slice10
  · exact point46Slice11
  · exact point46Slice12
  · exact point46Slice13
  · exact point46Slice14
  · exact point46Slice15
  · exact point46Slice16
  · exact point46Slice17
  · exact point46Slice18
  · exact point46Slice19
  · exact point46Slice20
  · exact point46Slice21
  · exact point46Slice22
  · exact point46Slice23
  · exact point46Slice24
  · exact point46Slice25
  · exact point46Slice26
  · exact point46Slice27
  · exact point46Slice28

set_option maxHeartbeats 1600000 in
private theorem point47Slice0 : pointSliceCheck 1 1680 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point47Slice1 : pointSliceCheck 1 1680 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point47Slice2 : pointSliceCheck 1 1680 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point47Slice3 : pointSliceCheck 1 1680 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point47Slice4 : pointSliceCheck 1 1680 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point47Slice5 : pointSliceCheck 1 1680 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point47Slice6 : pointSliceCheck 1 1680 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point47Slice7 : pointSliceCheck 1 1680 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point47Slice8 : pointSliceCheck 1 1680 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point47Slice9 : pointSliceCheck 1 1680 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point47Slice10 : pointSliceCheck 1 1680 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point47Slice11 : pointSliceCheck 1 1680 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point47Slice12 : pointSliceCheck 1 1680 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point47Slice13 : pointSliceCheck 1 1680 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point47Slice14 : pointSliceCheck 1 1680 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point47Slice15 : pointSliceCheck 1 1680 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point47Slice16 : pointSliceCheck 1 1680 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point47Slice17 : pointSliceCheck 1 1680 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point47Slice18 : pointSliceCheck 1 1680 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point47Slice19 : pointSliceCheck 1 1680 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point47Slice20 : pointSliceCheck 1 1680 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point47Slice21 : pointSliceCheck 1 1680 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point47Slice22 : pointSliceCheck 1 1680 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point47Slice23 : pointSliceCheck 1 1680 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point47Slice24 : pointSliceCheck 1 1680 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point47Slice25 : pointSliceCheck 1 1680 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point47Slice26 : pointSliceCheck 1 1680 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point47Slice27 : pointSliceCheck 1 1680 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point47Slice28 : pointSliceCheck 1 1680 28 := by
  decide +kernel

public theorem point47 : residualCheck 47 := by
  apply ofPointSlices 1 1680
  intro c
  fin_cases c
  · exact point47Slice0
  · exact point47Slice1
  · exact point47Slice2
  · exact point47Slice3
  · exact point47Slice4
  · exact point47Slice5
  · exact point47Slice6
  · exact point47Slice7
  · exact point47Slice8
  · exact point47Slice9
  · exact point47Slice10
  · exact point47Slice11
  · exact point47Slice12
  · exact point47Slice13
  · exact point47Slice14
  · exact point47Slice15
  · exact point47Slice16
  · exact point47Slice17
  · exact point47Slice18
  · exact point47Slice19
  · exact point47Slice20
  · exact point47Slice21
  · exact point47Slice22
  · exact point47Slice23
  · exact point47Slice24
  · exact point47Slice25
  · exact point47Slice26
  · exact point47Slice27
  · exact point47Slice28

set_option maxHeartbeats 1600000 in
private theorem point48Slice0 : pointSliceCheck 1 1686 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point48Slice1 : pointSliceCheck 1 1686 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point48Slice2 : pointSliceCheck 1 1686 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point48Slice3 : pointSliceCheck 1 1686 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point48Slice4 : pointSliceCheck 1 1686 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point48Slice5 : pointSliceCheck 1 1686 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point48Slice6 : pointSliceCheck 1 1686 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point48Slice7 : pointSliceCheck 1 1686 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point48Slice8 : pointSliceCheck 1 1686 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point48Slice9 : pointSliceCheck 1 1686 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point48Slice10 : pointSliceCheck 1 1686 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point48Slice11 : pointSliceCheck 1 1686 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point48Slice12 : pointSliceCheck 1 1686 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point48Slice13 : pointSliceCheck 1 1686 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point48Slice14 : pointSliceCheck 1 1686 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point48Slice15 : pointSliceCheck 1 1686 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point48Slice16 : pointSliceCheck 1 1686 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point48Slice17 : pointSliceCheck 1 1686 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point48Slice18 : pointSliceCheck 1 1686 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point48Slice19 : pointSliceCheck 1 1686 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point48Slice20 : pointSliceCheck 1 1686 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point48Slice21 : pointSliceCheck 1 1686 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point48Slice22 : pointSliceCheck 1 1686 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point48Slice23 : pointSliceCheck 1 1686 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point48Slice24 : pointSliceCheck 1 1686 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point48Slice25 : pointSliceCheck 1 1686 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point48Slice26 : pointSliceCheck 1 1686 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point48Slice27 : pointSliceCheck 1 1686 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point48Slice28 : pointSliceCheck 1 1686 28 := by
  decide +kernel

public theorem point48 : residualCheck 48 := by
  apply ofPointSlices 1 1686
  intro c
  fin_cases c
  · exact point48Slice0
  · exact point48Slice1
  · exact point48Slice2
  · exact point48Slice3
  · exact point48Slice4
  · exact point48Slice5
  · exact point48Slice6
  · exact point48Slice7
  · exact point48Slice8
  · exact point48Slice9
  · exact point48Slice10
  · exact point48Slice11
  · exact point48Slice12
  · exact point48Slice13
  · exact point48Slice14
  · exact point48Slice15
  · exact point48Slice16
  · exact point48Slice17
  · exact point48Slice18
  · exact point48Slice19
  · exact point48Slice20
  · exact point48Slice21
  · exact point48Slice22
  · exact point48Slice23
  · exact point48Slice24
  · exact point48Slice25
  · exact point48Slice26
  · exact point48Slice27
  · exact point48Slice28

set_option maxHeartbeats 1600000 in
private theorem point49Slice0 : pointSliceCheck 1 1688 0 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point49Slice1 : pointSliceCheck 1 1688 1 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point49Slice2 : pointSliceCheck 1 1688 2 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point49Slice3 : pointSliceCheck 1 1688 3 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point49Slice4 : pointSliceCheck 1 1688 4 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point49Slice5 : pointSliceCheck 1 1688 5 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point49Slice6 : pointSliceCheck 1 1688 6 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point49Slice7 : pointSliceCheck 1 1688 7 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point49Slice8 : pointSliceCheck 1 1688 8 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point49Slice9 : pointSliceCheck 1 1688 9 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point49Slice10 : pointSliceCheck 1 1688 10 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point49Slice11 : pointSliceCheck 1 1688 11 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point49Slice12 : pointSliceCheck 1 1688 12 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point49Slice13 : pointSliceCheck 1 1688 13 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point49Slice14 : pointSliceCheck 1 1688 14 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point49Slice15 : pointSliceCheck 1 1688 15 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point49Slice16 : pointSliceCheck 1 1688 16 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point49Slice17 : pointSliceCheck 1 1688 17 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point49Slice18 : pointSliceCheck 1 1688 18 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point49Slice19 : pointSliceCheck 1 1688 19 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point49Slice20 : pointSliceCheck 1 1688 20 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point49Slice21 : pointSliceCheck 1 1688 21 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point49Slice22 : pointSliceCheck 1 1688 22 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point49Slice23 : pointSliceCheck 1 1688 23 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point49Slice24 : pointSliceCheck 1 1688 24 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point49Slice25 : pointSliceCheck 1 1688 25 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point49Slice26 : pointSliceCheck 1 1688 26 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point49Slice27 : pointSliceCheck 1 1688 27 := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point49Slice28 : pointSliceCheck 1 1688 28 := by
  decide +kernel

public theorem point49 : residualCheck 49 := by
  apply ofPointSlices 1 1688
  intro c
  fin_cases c
  · exact point49Slice0
  · exact point49Slice1
  · exact point49Slice2
  · exact point49Slice3
  · exact point49Slice4
  · exact point49Slice5
  · exact point49Slice6
  · exact point49Slice7
  · exact point49Slice8
  · exact point49Slice9
  · exact point49Slice10
  · exact point49Slice11
  · exact point49Slice12
  · exact point49Slice13
  · exact point49Slice14
  · exact point49Slice15
  · exact point49Slice16
  · exact point49Slice17
  · exact point49Slice18
  · exact point49Slice19
  · exact point49Slice20
  · exact point49Slice21
  · exact point49Slice22
  · exact point49Slice23
  · exact point49Slice24
  · exact point49Slice25
  · exact point49Slice26
  · exact point49Slice27
  · exact point49Slice28

end Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Residual0Checks
